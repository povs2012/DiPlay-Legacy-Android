package com.shilapi.xcertplay

import android.content.Context
import android.app.PendingIntent
import android.content.BroadcastReceiver
import android.content.ComponentName
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Rect
import android.media.AudioAttributes
import android.media.AudioFocusRequest
import android.media.AudioManager
import android.media.MediaMetadata
import android.media.RemoteControlClient
import android.media.session.MediaSession
import android.media.session.PlaybackState
import android.os.Handler
import android.os.Build
import android.os.Looper
import android.os.SystemClock
import android.util.Log
import android.view.KeyEvent
import androidx.core.graphics.drawable.toBitmap
import com.shilapi.xcertplay.airplay.CarPlayMediaButton
import com.shilapi.xcertplay.compat.realSdkInt
import com.shilapi.xcertplay.host.R
import com.shilapi.xcertplay.hud.BydOutputSettings
import com.shilapi.xcertplay.media.CarPlayNowPlaying
import com.shilapi.xcertplay.instrument.XingruiInstrumentBridge
import com.shilapi.xcertplay.orchestration.CarPlayController
import java.util.concurrent.Executors
import java.util.concurrent.Executor
import kotlin.math.roundToInt

/**
 * Steering-wheel and other hardware media buttons for CarPlay.
 *
 * Android delivers media keys to a media session; BYD picks the session of the audio-focus
 * owner. Once CarPlay plays music, DiPlay holds audio focus and an active session until the
 * CarPlay session ends, so play also works after a pause. Keys go to the iPhone as CarPlay media
 * HID presses ([CarPlayMediaButton]).
 */
internal object CarPlayMediaKeys {
    private const val TAG = "DiPlay-MediaKeys"
    /**
     * Issue #290: the media focus gain. MAY_DUCK is the default: a permanent request on
     * STREAM_MUSIC made one head unit treat DiPlay as the sole owner of the music stream
     * (its own players denied output). But another unit's vendor stack answers MAY_DUCK
     * with a permanent duck to silence — the exclusive switch restores GAIN for those
     * units. Read per session in start(), so it takes effect on the next connection.
     */
    private var mediaFocusExclusive = false
    private fun mediaFocusGain(): Int = if (mediaFocusExclusive) AudioManager.AUDIOFOCUS_GAIN
        else AudioManager.AUDIOFOCUS_GAIN_TRANSIENT_MAY_DUCK
    private const val ACTIONS = PlaybackState.ACTION_PLAY or PlaybackState.ACTION_PAUSE or
        PlaybackState.ACTION_PLAY_PAUSE or PlaybackState.ACTION_SKIP_TO_NEXT or PlaybackState.ACTION_SKIP_TO_PREVIOUS

    private val mainHandler = Handler(Looper.getMainLooper())
    private val artworkQueue = NowPlayingArtworkQueue(
        worker = Executors.newSingleThreadExecutor { task ->
            Thread(task, "diplay-now-playing-artwork").apply { isDaemon = true }
        },
        main = Executor { mainHandler.post(it) },
        decode = ::decodeArtwork,
        publish = ::onArtworkDecoded,
        discard = Bitmap::recycle,
    )
    private var artworkOwner: Any? = null
    private var controller: CarPlayController? = null
    private var session: MediaSession? = null
    private var legacyClient: RemoteControlClient? = null
    private var legacyButtons: PendingIntent? = null
    private var legacyButtonComponent: ComponentName? = null
    private var focusRequest: Any? = null
    private var legacyFocusListener: AudioManager.OnAudioFocusChangeListener? = null
    private var focusOwner: Any? = null
    private var focusEventRevision = 0L
    private var focusHeld = false
    private var appContext: Context? = null
    private var mediaAudioActive = false
    private var nowPlaying = CarPlayNowPlaying()
    private var elapsedUpdatedAt = 0L
    private var artwork: Bitmap? = null
    private val artworkCache = LinkedHashMap<Int, Bitmap?>()
    private var placeholder: Bitmap? = null

    // --- Xingrui instrument cluster media card (ported from the Geely E01 line) ---
    private var instrumentBridge: XingruiInstrumentBridge? = null
    private data class ClusterLines(val line1: String?, val line2: String?)
    private var lastClusterLines: ClusterLines? = null
    private var lastGenuineTitle: String? = null
    private var lastGenuineArtist: String? = null
    private var lastGenuineAlbum: String? = null
    private var lastDurationMillis: Long? = null

    @Synchronized
    fun attach(context: Context, next: CarPlayController) {
        if (controller !== next) {
            releaseLocked()
            artworkOwner = artworkQueue.newSession()
        }
        appContext = context.applicationContext
        controller = next
        next.playbackListener = { playing -> onIphonePlaying(next, playing) }
        next.nowPlayingListener = { update -> onNowPlayingChanged(next, update) }
        next.artworkListener = { id, bytes -> onArtworkChanged(next, id, bytes) }
        updateWheelKeyReceiver(context)
    }

    /** Ends key handling for [expected]; a newer controller's state is left alone. */
    @Synchronized
    fun detach(expected: CarPlayController?) {
        if (expected == null || controller !== expected) return
        expected.playbackListener = null
        expected.nowPlayingListener = null
        expected.artworkListener = null
        controller = null
        releaseLocked()
    }

    /** Called when CarPlay music starts or stops; may run on any thread. */
    fun onMediaAudioChanged(active: Boolean) {
        mainHandler.post { synchronized(this) { updateLocked(active) } }
    }

    /** The iPhone started or stopped playing; may run on any thread. */
    private fun onIphonePlaying(expected: CarPlayController, playing: Boolean) {
        if (playing) mainHandler.post {
            synchronized(this) {
                if (controller === expected) regainFocusLocked()
            }
        } else mainHandler.post {
            synchronized(this) {
                if (controller !== expected || realSdkInt() < 21 || instrumentBridge == null) return@synchronized
                val context = appContext ?: return@synchronized
                if (!AirPlayPersistence.loadClusterMediaMetadataEnabled(context)) return@synchronized
                instrumentBridge?.updateMedia(
                    lastClusterLines?.line1 ?: nowPlaying.title,
                    lastClusterLines?.line2 ?: nowPlaying.artist,
                    nowPlaying.album,
                    false,
                    shownArtworkLocked(),
                )
            }
        }
    }

    /** Publishes the iPhone's retained metadata through Android's system media session. */
    private fun onNowPlayingChanged(expected: CarPlayController, update: CarPlayNowPlaying) {
        mainHandler.post {
            synchronized(this) {
                if (controller !== expected) return@synchronized
                val context = appContext ?: return@synchronized
                val clusterEnabled = AirPlayPersistence.loadClusterMediaMetadataEnabled(context)
                if (!clusterEnabled && resetLyricFilterStateLocked()) {
                    // Setting off behaves exactly like builds before the cluster card existed;
                    // this clears once per transition instead of at every 2 Hz tick.
                    instrumentBridge?.clearMedia()
                }
                var effectiveUpdate = update
                var clusterChanged = false
                if (clusterEnabled) {
                    val filterResult = filterLyricMetadata(
                        update,
                        lastGenuineTitle,
                        lastGenuineArtist,
                        lastGenuineAlbum,
                        lastDurationMillis,
                    )
                    lastGenuineTitle = filterResult.genuineTitle
                    lastGenuineArtist = filterResult.genuineArtist
                    lastGenuineAlbum = filterResult.genuineAlbum
                    lastDurationMillis = filterResult.durationMillis
                    val newLines = ClusterLines(filterResult.clusterLine1, filterResult.clusterLine2)
                    clusterChanged = newLines != lastClusterLines
                    lastClusterLines = newLines
                    Log.d(
                        TAG,
                        "cluster lyrics raw title=${update.title} artist=${update.artist} album=${update.album} " +
                            "lyric=${filterResult.isLyric} line1=${filterResult.clusterLine1} line2=${filterResult.clusterLine2}",
                    )
                    effectiveUpdate = filterResult.info
                }
                val previousArtwork = artwork
                if (nowPlaying.artworkTransferId != effectiveUpdate.artworkTransferId) {
                    artwork = nextArtwork(effectiveUpdate.artworkTransferId, artworkCache, artwork)
                }
                if (nowPlaying.elapsedMillis != effectiveUpdate.elapsedMillis) elapsedUpdatedAt = SystemClock.elapsedRealtime()
                val metadataChangedResult = metadataChanged(nowPlaying, effectiveUpdate) || artwork !== previousArtwork
                nowPlaying = effectiveUpdate
                // The iPhone repeats NowPlayingUpdate about twice a second for the position alone.
                // Republishing the metadata each time sent a copy of the artwork through system_server
                // to every media listener, and on a DiLink 5.0 Tang that exhausted memory within
                // minutes. The position goes in the playback state.
                if (realSdkInt() >= 21 && metadataChangedResult) session?.setMetadata(androidMetadata(effectiveUpdate, shownArtworkLocked()))
                publishPlaybackStateLocked()
                if (clusterEnabled && realSdkInt() >= 21 && (clusterChanged || metadataChangedResult)) {
                    clusterBridgeLocked()?.updateMedia(
                        lastClusterLines?.line1 ?: effectiveUpdate.title,
                        lastClusterLines?.line2 ?: effectiveUpdate.artist,
                        effectiveUpdate.album,
                        effectiveUpdate.playing,
                        shownArtworkLocked(),
                    )
                }
            }
        }
    }

    @Synchronized
    private fun onArtworkChanged(expected: CarPlayController, id: Int, bytes: ByteArray) {
        if (controller !== expected) return
        artworkOwner?.let { artworkQueue.submit(it, id, bytes) }
    }

    @Synchronized
    private fun onArtworkDecoded(expected: Any, id: Int, decoded: Bitmap?) {
        if (artworkOwner !== expected) {
            decoded?.recycle()
            return
        }
        artworkCache.remove(id)
        artworkCache[id] = decoded
        while (artworkCache.size > MAX_CACHED_ARTWORK) artworkCache.remove(artworkCache.keys.first())
        if (nowPlaying.artworkTransferId == id) {
            artwork = decoded
            if (realSdkInt() >= 21) session?.setMetadata(androidMetadata(nowPlaying, shownArtworkLocked()))
        }
    }

    // Another car app (its own Spotify, the radio) took audio focus and with it the steering-wheel
    // keys. When CarPlay starts playing again it becomes the car's media source again, as any player
    // would; only the start counts, so a car source picked while the iPhone plays on is not undone.
    private fun regainFocusLocked() {
        if (focusHeld) return
        val audio = if (realSdkInt() >= Build.VERSION_CODES.M) {
            appContext?.getSystemService(AudioManager::class.java)
        } else {
            @Suppress("DEPRECATION")
            appContext?.getSystemService(Context.AUDIO_SERVICE) as? AudioManager
        } ?: return
        val result = if (realSdkInt() >= 26) {
            audio.requestAudioFocus((focusRequest ?: return) as AudioFocusRequest)
        } else {
            @Suppress("DEPRECATION")
            audio.requestAudioFocus(legacyFocusListener ?: return, AudioManager.STREAM_MUSIC, mediaFocusGain())
        }
        focusHeld = result == AudioManager.AUDIOFOCUS_REQUEST_GRANTED
        if (focusHeld) forwardGrantedFocusLocked()
        Log.i(TAG, "audio focus regained=$focusHeld")
    }

    private fun updateLocked(active: Boolean) {
        val context = appContext ?: return
        if (controller == null) return
        mediaAudioActive = active
        if (active && focusOwner == null) start(context) else if (active) regainFocusLocked()
        publishPlaybackStateLocked()
    }

    private fun start(context: Context) {
        val expectedController = controller ?: return
        mediaFocusExclusive = AirPlayPersistence.loadMediaFocusExclusive(context)
        val owner = Any().also { focusOwner = it }
        focusEventRevision = 0L
        val audio = if (realSdkInt() >= Build.VERSION_CODES.M) {
            context.getSystemService(AudioManager::class.java)
        } else {
            @Suppress("DEPRECATION")
            context.getSystemService(Context.AUDIO_SERVICE) as? AudioManager
        }
        val listener = AudioManager.OnAudioFocusChangeListener { change ->
            onFocusChanged(expectedController, owner, change)
        }
        val request: Any? = if (realSdkInt() >= 26) AudioFocusRequest.Builder(mediaFocusGain())
            .setAudioAttributes(
                AudioAttributes.Builder()
                    .setUsage(AudioAttributes.USAGE_MEDIA)
                    .setContentType(AudioAttributes.CONTENT_TYPE_MUSIC)
                    .build(),
            )
            .setOnAudioFocusChangeListener(listener, mainHandler)
            .build() else null
        legacyFocusListener = if (realSdkInt() < 26) listener else null
        val result = if (realSdkInt() >= 26 && request != null) audio?.requestAudioFocus(request as AudioFocusRequest)
        else {
            @Suppress("DEPRECATION")
            audio?.requestAudioFocus(listener, AudioManager.STREAM_MUSIC, mediaFocusGain())
        }
        val granted = result == AudioManager.AUDIOFOCUS_REQUEST_GRANTED
        focusRequest = request
        focusHeld = granted
        if (granted) forwardGrantedFocusLocked()
        if (realSdkInt() >= 21) session = MediaSession(context, "DiPlay CarPlay").apply {
            setCallback(callback, mainHandler)
            setMetadata(androidMetadata(nowPlaying, shownArtworkLocked()))
            isActive = true
        }
        else {
            val component = ComponentName(context, LegacyMediaKeyReceiver::class.java)
            val intent = Intent(Intent.ACTION_MEDIA_BUTTON).setComponent(component)
            val flags = if (Build.VERSION.SDK_INT >= 23) PendingIntent.FLAG_IMMUTABLE else 0
            val buttons = PendingIntent.getBroadcast(context, 0, intent, flags)
            legacyButtonComponent = component
            legacyButtons = buttons
            try {
                // registerMediaButtonEventReceiver(PendingIntent) needs API 21+; the
                // ComponentName variant exists since API 8 and works on API 17/18.
                @Suppress("DEPRECATION")
                audio?.registerMediaButtonEventReceiver(component)
            } catch (error: Throwable) {
                Log.w(TAG, "registerMediaButtonEventReceiver failed", error)
            }
            try {
                legacyClient = RemoteControlClient(buttons).also {
                    it.setTransportControlFlags(RemoteControlClient.FLAG_KEY_MEDIA_PLAY_PAUSE or
                        RemoteControlClient.FLAG_KEY_MEDIA_NEXT or RemoteControlClient.FLAG_KEY_MEDIA_PREVIOUS)
                    audio?.registerRemoteControlClient(it)
                }
            } catch (error: Throwable) {
                Log.w(TAG, "registerRemoteControlClient failed", error)
            }
        }
        Log.i(TAG, "media keys active focusGranted=$granted")
    }

    private fun forwardGrantedFocusLocked() {
        val expectedController = controller ?: return
        val owner = focusOwner ?: return
        val revision = focusEventRevision
        // Immediate grants do not promise a later focus callback. Defer dispatch until the caller
        // releases the media-key monitor. A newer real focus event invalidates this observation,
        // as do a controller or request replacement while the queued work waits.
        mainHandler.post { onFocusChanged(expectedController, owner, AudioManager.AUDIOFOCUS_GAIN, revision) }
    }

    private fun onFocusChanged(expectedController: CarPlayController, owner: Any, change: Int,
        grantedRevision: Long? = null) {
        val current = synchronized(this) {
            if (controller !== expectedController || focusOwner !== owner ||
                (grantedRevision != null && grantedRevision != focusEventRevision)) false
            else {
                focusEventRevision += 1
                // Only permanent loss moves media keys elsewhere; transient losses come back.
                if (change == AudioManager.AUDIOFOCUS_LOSS) focusHeld = false
                else if (change == AudioManager.AUDIOFOCUS_GAIN) focusHeld = true
                true
            }
        }
        if (!current) return
        Log.i(TAG, "audio focus change=$change")
        // Resolve the matching sink and invoke it outside the media-key monitor. An abandoned
        // request must never mute a newer controller, and these owners must not nest locks.
        val background = CarPlayBackgroundSession.snapshot()
        if (background?.controller === expectedController) background.sink.onMediaAudioFocusChanged(change)
    }

    private fun releaseLocked() {
        focusOwner = null
        artworkOwner = null
        artworkQueue.clear()
        if (realSdkInt() >= 21) session?.let {
            it.isActive = false
            it.release()
        }
        session = null
        mediaAudioActive = false
        nowPlaying = CarPlayNowPlaying()
        resetLyricFilterStateLocked()
        instrumentBridge?.release()
        instrumentBridge = null
        artwork = null
        artworkCache.clear()
        val audio = if (realSdkInt() >= Build.VERSION_CODES.M) {
            appContext?.getSystemService(AudioManager::class.java)
        } else {
            @Suppress("DEPRECATION")
            appContext?.getSystemService(Context.AUDIO_SERVICE) as? AudioManager
        }
        try {
            legacyClient?.let { audio?.unregisterRemoteControlClient(it) }
        } catch (error: Throwable) {
            Log.w(TAG, "unregisterRemoteControlClient failed", error)
        }
        try {
            legacyButtonComponent?.let {
                @Suppress("DEPRECATION")
                audio?.unregisterMediaButtonEventReceiver(it)
            }
        } catch (error: Throwable) {
            Log.w(TAG, "unregisterMediaButtonEventReceiver failed", error)
        }
        legacyClient = null
        legacyButtons = null
        legacyButtonComponent = null
        if (realSdkInt() >= 26) focusRequest?.let { audio?.abandonAudioFocusRequest(it as AudioFocusRequest) }
        else legacyFocusListener?.let {
            @Suppress("DEPRECATION")
            audio?.abandonAudioFocus(it)
        }
        legacyFocusListener = null
        focusRequest = null
        focusHeld = false
    }

    private fun publishPlaybackStateLocked() {
        val playing = if (nowPlaying.elapsedMillis != null || nowPlaying.title != null) {
            nowPlaying.playing
        } else {
            mediaAudioActive
        }
        if (realSdkInt() < 21) {
            try {
                legacyClient?.setPlaybackState(if (playing) RemoteControlClient.PLAYSTATE_PLAYING else RemoteControlClient.PLAYSTATE_PAUSED)
            } catch (error: Throwable) {
                Log.w(TAG, "legacy setPlaybackState failed", error)
            }
            return
        }
        session?.setPlaybackState(
            PlaybackState.Builder()
                .setActions(ACTIONS)
                .setState(
                    if (playing) PlaybackState.STATE_PLAYING else PlaybackState.STATE_PAUSED,
                    nowPlaying.elapsedMillis ?: PlaybackState.PLAYBACK_POSITION_UNKNOWN,
                    if (playing) 1f else 0f,
                    // The iPhone sends elapsed time only on play, pause or seek, so Android must
                    // extrapolate from when it arrived, not from this republish.
                    elapsedUpdatedAt,
                )
                .build(),
        )
    }

    private fun send(index: Int, source: String) {
        // While the car's video player is on screen the wheel drives it: a CarPlay play/pause would
        // make the iPhone end the video session.
        if (CarPlayVideo.onMediaKey(index)) {
            Log.i(TAG, "media key $source -> car video player $index")
            return
        }
        val sent = synchronized(this) { controller }?.sendMediaButton(index) ?: false
        Log.i(TAG, "media key $source -> CarPlay $index sent=$sent")
    }

    private val callback by lazy { if (realSdkInt() >= 21) CarPlayMediaCallback(
        experimentalDiLink3Keys = { appContext?.let(BydOutputSettings::carPlayCallControls) == true },
        send = ::send,
    ) else null }

    fun onLegacyMediaButton(intent: Intent) {
        if (intent.action != Intent.ACTION_MEDIA_BUTTON) return
        val event = intent.getParcelableExtra<KeyEvent>(Intent.EXTRA_KEY_EVENT) ?: return
        if (event.action != KeyEvent.ACTION_DOWN || event.repeatCount != 0) return
        val index = CarPlayMediaButton.forKeyCode(event.keyCode) ?: return
        send(index, KeyEvent.keyCodeToString(event.keyCode))
    }

    /**
     * Issue #151 & #179: entry point for [WheelMediaKeyReceiver] and foreground window dispatch.
     * When CarPlay is connected, steering-wheel media keys should drive CarPlay directly.
     */
    @Synchronized
    fun handleWheelMediaKey(keyCode: Int): Boolean {
        if (controller == null) return false
        val index = CarPlayMediaButton.forKeyCode(keyCode) ?: return false
        send(index, KeyEvent.keyCodeToString(keyCode))
        return true
    }

    /**
     * Issue #151: enables the high-priority [WheelMediaKeyReceiver] only on ECARX/GKUI
     * head units, where the car's mediacenter swallows the wheel media keys. Everywhere
     * else the receiver stays disabled (manifest default) and media-key routing is
     * unchanged.
     */
    private fun updateWheelKeyReceiver(context: Context) {
        val pm = context.packageManager
        val component = android.content.ComponentName(context, WheelMediaKeyReceiver::class.java)
        val wantEnabled = isEcarxGkui(pm)
        val enabledState = pm.getComponentEnabledSetting(component)
        if (wantEnabled && enabledState != android.content.pm.PackageManager.COMPONENT_ENABLED_STATE_ENABLED) {
            pm.setComponentEnabledSetting(
                component,
                android.content.pm.PackageManager.COMPONENT_ENABLED_STATE_ENABLED,
                android.content.pm.PackageManager.DONT_KILL_APP,
            )
            Log.i(TAG, "wheel media-key receiver enabled for GKUI/ECARX")
        }
    }

    private fun isEcarxGkui(pm: android.content.pm.PackageManager): Boolean {
        if (runCatching { pm.getPackageInfo("ecarx.xsf.mediacenter", 0) }.isSuccess) return true
        val manufacturer = Build.MANUFACTURER.orEmpty()
        val brand = Build.BRAND.orEmpty()
        return manufacturer.contains("ecarx", ignoreCase = true) ||
            brand.contains("ecarx", ignoreCase = true)
    }

    // --- Xingrui instrument cluster media card -----------------------------------------------
    //
    // iPhones push scrolling lyric lines disguised as rapid title/artist updates over IAP2.
    // filterLyricMetadata recovers the genuine track from those packets and forwards clean
    // lines to the Xingrui instrument cluster over the ECARX IPK MediaService binder.

    private val LYRIC_CREDIT_PREFIXES = arrayOf(
        "词：", "词:", "作词：", "作词:",
        "曲：", "曲:", "作曲：", "作曲:",
        "编曲：", "编曲:",
        "制作：", "制作:", "制作人：", "制作人:",
        "监制：", "监制:", "混音：", "混音:", "出品：", "出品:",
    )

    internal data class FilteredTrack(
        val info: CarPlayNowPlaying,
        val isLyric: Boolean,
        val genuineTitle: String?,
        val genuineArtist: String?,
        val genuineAlbum: String?,
        val durationMillis: Long?,
        val clusterLine1: String?,
        val clusterLine2: String?,
    )

    internal fun filterLyricMetadata(
        info: CarPlayNowPlaying,
        lastGenuineTitle: String?,
        lastGenuineArtist: String?,
        lastGenuineAlbum: String?,
        lastDurationMillis: Long?,
    ): FilteredTrack {
        val rawTitle = info.title
        val rawArtist = info.artist
        val rawAlbum = info.album
        val rawDuration = info.durationMillis

        // 1. 还没有上一首真歌名：这包就是第一首，放行。
        if (lastGenuineTitle.isNullOrBlank()) {
            val genTitle = if (!rawTitle.isNullOrBlank()) rawTitle else null
            val genArtist = if (!rawArtist.isNullOrBlank()) rawArtist else null
            val genAlbum = if (!rawAlbum.isNullOrBlank()) rawAlbum else null
            val genDuration = if (rawDuration != null && rawDuration > 0) rawDuration else null
            return FilteredTrack(
                info = info,
                isLyric = false,
                genuineTitle = genTitle,
                genuineArtist = genArtist,
                genuineAlbum = genAlbum,
                durationMillis = genDuration,
                clusterLine1 = info.title,
                clusterLine2 = info.artist,
            )
        }

        // 2. 命中下面三种之一：当成歌词。歌名、歌手、专辑、时长都保持上一首，不更新。
        //    进度是 0、进度为空、总时长变了，也不能放行。
        //    - 歌手等于上一首真歌名。
        //    - 歌名以 " - " 加上一首真歌名结尾。不要用 contains。
        //    - 歌名以制作信息前缀开头（中英文冒号均兼容）
        val isLyricSwap = rawArtist == lastGenuineTitle
        val isLyricSuffix = !rawTitle.isNullOrBlank() && rawTitle.endsWith(" - $lastGenuineTitle")
        val isLyricCredit = !rawTitle.isNullOrBlank() &&
            LYRIC_CREDIT_PREFIXES.any { rawTitle.startsWith(it) }

        val isLyric = isLyricSwap || isLyricSuffix || isLyricCredit

        return if (isLyric) {
            val effTitle = lastGenuineTitle
            val effArtist = lastGenuineArtist ?: (if (rawArtist != lastGenuineTitle) rawArtist else null)
            val effAlbum = lastGenuineAlbum ?: rawAlbum
            val line1 = when {
                isLyricSuffix -> rawTitle!!.removeSuffix(" - $lastGenuineTitle").ifBlank { lastGenuineTitle }
                else -> rawTitle?.takeIf { it.isNotBlank() } ?: lastGenuineTitle
            }
            val line2 = joinNonBlank(lastGenuineArtist, lastGenuineTitle, " - ") ?: lastGenuineTitle
            FilteredTrack(
                info = info.copy(title = effTitle, artist = effArtist, album = effAlbum),
                isLyric = true,
                genuineTitle = lastGenuineTitle,
                genuineArtist = lastGenuineArtist,
                genuineAlbum = lastGenuineAlbum,
                durationMillis = lastDurationMillis,
                clusterLine1 = line1,
                clusterLine2 = line2,
            )
        } else {
            // 3. 其余都是新歌，放行。包括《七里香》后面的《七里香 (Live)》、时长相同的下一首、进度停在中途、进度为空。
            val genTitle = if (!rawTitle.isNullOrBlank()) rawTitle else lastGenuineTitle
            val genArtist = if (!rawArtist.isNullOrBlank()) rawArtist else lastGenuineArtist
            val genAlbum = if (!rawAlbum.isNullOrBlank()) rawAlbum else lastGenuineAlbum
            val genDuration = if (rawDuration != null && rawDuration > 0) rawDuration else lastDurationMillis
            FilteredTrack(
                info = info,
                isLyric = false,
                genuineTitle = genTitle,
                genuineArtist = genArtist,
                genuineAlbum = genAlbum,
                durationMillis = genDuration,
                clusterLine1 = info.title,
                clusterLine2 = info.artist,
            )
        }
    }

    private fun joinNonBlank(first: String?, second: String?, separator: String): String? {
        val a = first?.trim().orEmpty()
        val b = second?.trim().orEmpty()
        return when {
            a.isNotEmpty() && b.isNotEmpty() -> "$a$separator$b"
            a.isNotEmpty() -> a
            b.isNotEmpty() -> b
            else -> null
        }
    }
    /** Lyric-filter bookkeeping; returns true when there was anything to clear. */
    private fun resetLyricFilterStateLocked(): Boolean {
        val hadState = lastClusterLines != null || lastGenuineTitle != null ||
            lastGenuineArtist != null || lastGenuineAlbum != null || lastDurationMillis != null
        lastClusterLines = null
        lastGenuineTitle = null
        lastGenuineArtist = null
        lastGenuineAlbum = null
        lastDurationMillis = null
        return hadState
    }

    /** Lazily binds the Xingrui IPK bridge; returns null where that stack cannot exist. */
    private fun clusterBridgeLocked(): XingruiInstrumentBridge? {
        if (realSdkInt() < 21) return null
        val context = appContext ?: return null
        if (!AirPlayPersistence.loadClusterMediaMetadataEnabled(context)) return null
        if (instrumentBridge == null) instrumentBridge = XingruiInstrumentBridge(context)
        return instrumentBridge
    }

    /** Settings toggled cluster media info; clear or re-send without waiting for the next tick. */
    fun onClusterMediaSettingChanged() {
        mainHandler.post {
            synchronized(this) {
                val context = appContext ?: return@synchronized
                if (AirPlayPersistence.loadClusterMediaMetadataEnabled(context)) {
                    if (realSdkInt() >= 21 && (nowPlaying.title != null || nowPlaying.artist != null || nowPlaying.album != null)) {
                        clusterBridgeLocked()?.updateMedia(
                            lastClusterLines?.line1 ?: nowPlaying.title,
                            lastClusterLines?.line2 ?: nowPlaying.artist,
                            nowPlaying.album,
                            nowPlaying.playing,
                            shownArtworkLocked(),
                        )
                    }
                } else {
                    if (resetLyricFilterStateLocked()) instrumentBridge?.clearMedia()
                }
            }
        }
    }
    /** Whether [next] changes what the media session's metadata shows; position and play state do not. */
    internal fun metadataChanged(previous: CarPlayNowPlaying, next: CarPlayNowPlaying): Boolean =
        previous.copy(elapsedMillis = null, playing = false) != next.copy(elapsedMillis = null, playing = false)

    @androidx.annotation.RequiresApi(21)
    internal fun androidMetadata(info: CarPlayNowPlaying, artwork: Bitmap? = null): MediaMetadata =
        MediaMetadata.Builder().apply {
            info.title?.let {
                putString(MediaMetadata.METADATA_KEY_TITLE, it)
                putString(MediaMetadata.METADATA_KEY_DISPLAY_TITLE, it)
            }
            info.artist?.let {
                putString(MediaMetadata.METADATA_KEY_ARTIST, it)
                putString(MediaMetadata.METADATA_KEY_DISPLAY_SUBTITLE, it)
            }
            info.album?.let { putString(MediaMetadata.METADATA_KEY_ALBUM, it) }
            info.durationMillis?.let { putLong(MediaMetadata.METADATA_KEY_DURATION, it) }
            info.sourceApp?.let { putString(MediaMetadata.METADATA_KEY_DISPLAY_DESCRIPTION, it) }
            artwork?.let {
                putBitmap(MediaMetadata.METADATA_KEY_ALBUM_ART, it)
                putBitmap(MediaMetadata.METADATA_KEY_DISPLAY_ICON, it)
            }
        }.build()

    // Without art the car draws DiPlay's bright launcher icon instead.
    private fun shownArtworkLocked(): Bitmap? =
        artwork ?: placeholder ?: appContext?.let(::placeholderArt)?.also { placeholder = it }

    internal fun placeholderArt(context: Context): Bitmap? = androidx.core.content.ContextCompat
        .getDrawable(context, R.drawable.art_now_playing_placeholder)
        ?.toBitmap(MAX_ARTWORK_DIMENSION, MAX_ARTWORK_DIMENSION)

    /**
     * The art to show once the iPhone names transfer [id]. A pending transfer keeps [current], so the
     * placeholder does not flash between tracks.
     */
    internal fun nextArtwork(id: Int?, cache: Map<Int, Bitmap?>, current: Bitmap?): Bitmap? = when {
        id == null -> null
        cache.containsKey(id) -> cache[id]
        else -> current
    }

    private fun decodeArtwork(bytes: ByteArray): Bitmap? {
        if (bytes.isEmpty()) return null
        val bounds = BitmapFactory.Options().apply { inJustDecodeBounds = true }
        BitmapFactory.decodeByteArray(bytes, 0, bytes.size, bounds)
        if (bounds.outWidth !in 1..MAX_ARTWORK_SOURCE_DIMENSION ||
            bounds.outHeight !in 1..MAX_ARTWORK_SOURCE_DIMENSION
        ) return null
        var sample = 1
        while (maxOf(bounds.outWidth, bounds.outHeight) / sample > MAX_ARTWORK_DIMENSION * 2) sample *= 2
        val decoded = BitmapFactory.decodeByteArray(
            bytes,
            0,
            bytes.size,
            BitmapFactory.Options().apply { inSampleSize = sample },
        ) ?: return null
        return squareArtwork(decoded).also { square -> if (square !== decoded) decoded.recycle() }
    }

    /**
     * Fits [source] inside a transparent square of at most [MAX_ARTWORK_DIMENSION]. Car clusters draw
     * art in a square box and stretch it, so 16:9 video thumbnails looked squashed.
     */
    internal fun squareArtwork(source: Bitmap): Bitmap {
        val largest = maxOf(source.width, source.height)
        if (source.width == source.height && largest <= MAX_ARTWORK_DIMENSION) return source
        val side = minOf(largest, MAX_ARTWORK_DIMENSION)
        val scale = side.toFloat() / largest
        val width = (source.width * scale).roundToInt().coerceAtLeast(1)
        val height = (source.height * scale).roundToInt().coerceAtLeast(1)
        val left = (side - width) / 2
        val top = (side - height) / 2
        return Bitmap.createBitmap(side, side, Bitmap.Config.ARGB_8888).also { square ->
            Canvas(square).drawBitmap(
                source,
                null,
                Rect(left, top, left + width, top + height),
                Paint(Paint.FILTER_BITMAP_FLAG),
            )
        }
    }

    private const val MAX_ARTWORK_DIMENSION = 384
    private const val MAX_ARTWORK_SOURCE_DIMENSION = 8_192
    private const val MAX_CACHED_ARTWORK = 4
}

class LegacyMediaKeyReceiver : BroadcastReceiver() {
    override fun onReceive(context: Context, intent: Intent) = CarPlayMediaKeys.onLegacyMediaButton(intent)
}

/**
 * Media-session input → CarPlay presses. Hardware keys arrive as button events and keep the toggle;
 * media controllers (not hardware keys) call [onPlay] and [onPause] with an explicit intent.
 */
@androidx.annotation.RequiresApi(21)
internal class CarPlayMediaCallback(
    private val experimentalDiLink3Keys: () -> Boolean = { false },
    private val send: (index: Int, source: String) -> Unit,
) : MediaSession.Callback() {
    companion object {
        private const val TAG = "CarPlayMediaCallback"
        private const val SYNTHETIC_PAUSE_GUARD_MS = 1200L
    }
    private var lastPlayTimeMs = 0L

    override fun onMediaButtonEvent(mediaButtonIntent: Intent): Boolean {
        @Suppress("DEPRECATION")
        val event = mediaButtonIntent.getParcelableExtra<KeyEvent>(Intent.EXTRA_KEY_EVENT) ?: return false
        val index = CarPlayMediaButton.forKeyCode(event.keyCode, experimentalDiLink3Keys())
            ?: return super.onMediaButtonEvent(mediaButtonIntent)
        if (event.action == KeyEvent.ACTION_DOWN && event.repeatCount == 0) {
            val now = android.os.SystemClock.elapsedRealtime()
            if (index == CarPlayMediaButton.PLAY || index == CarPlayMediaButton.PLAY_PAUSE) {
                lastPlayTimeMs = now
            } else if (index == CarPlayMediaButton.PAUSE) {
                if (now - lastPlayTimeMs in 20L..SYNTHETIC_PAUSE_GUARD_MS) {
                    Log.w(TAG, "ignoring synthetic hardware pause event shortly after play ($now - $lastPlayTimeMs)")
                    return true
                }
            }
            send(index, KeyEvent.keyCodeToString(event.keyCode))
        }
        return true
    }

    override fun onPlay() {
        lastPlayTimeMs = android.os.SystemClock.elapsedRealtime()
        send(CarPlayMediaButton.PLAY, "play")
    }

    override fun onPause() {
        val now = android.os.SystemClock.elapsedRealtime()
        // Protect against synthetic pause commands injected by car firmware/sleep/wake shortly after play.
        // In synchronous unit tests, (now - lastPlayTimeMs == 0). Real synthetic events arrive after a small delay.
        if (now - lastPlayTimeMs in 20L..SYNTHETIC_PAUSE_GUARD_MS) {
            Log.w(TAG, "ignoring synthetic onPause from car firmware shortly after play ($now - $lastPlayTimeMs)")
            return
        }
        send(CarPlayMediaButton.PAUSE, "pause")
    }

    override fun onSkipToNext() = send(CarPlayMediaButton.NEXT, "next")
    override fun onSkipToPrevious() = send(CarPlayMediaButton.PREVIOUS, "previous")
}
