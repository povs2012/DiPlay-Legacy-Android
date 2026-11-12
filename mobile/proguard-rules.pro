# Rules the release package needs because of how this app reaches a class, not because R8 guessed wrong.
#
# Everything else is left to R8: the app calls its own code directly, and every class named in the
# manifest or in a layout is kept by the rules the Android plugin generates from those files.

# --- What a field report has to stay readable for ------------------------------------------------
#
# The package carries "Save diagnostic report", and what comes back is read by a person: a stack
# trace full of `a.b.c` names cannot be matched to this source. So this app's own classes keep
# their names, and line numbers are kept with them. Third-party names are still rewritten, which
# is where the size is.
-keepnames class com.shilapi.xcertplay.**
-keepattributes SourceFile,LineNumberTable

# --- Libraries compiled against platform internals ----------------------------------------------
#
# conscrypt references the KitKat-era platform SSL internals (com.android.org.conscrypt /
# org.apache.harmony.xnet.provider.jsse) that exist only on old devices; both references are
# unreachable-or-optional here and R8 reports them as missing classes rather than optionals.
# Dontwarn says "known absent, do not stop the build"; it does not keep anything.
-dontwarn com.android.org.conscrypt.SSLParametersImpl
-dontwarn org.apache.harmony.xnet.provider.jsse.SSLParametersImpl
-dontwarn org.conscrypt.**
