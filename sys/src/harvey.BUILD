CMD_DEPS = [
	"//sys/src/libavl:libavl",
	"//sys/src/libcomplete:libcomplete",
	"//sys/src/libcontrol:libcontrol",
	"//sys/src/libdisk:libdisk",
	"//sys/src/libflate:libflate",
	"//sys/src/libframe:libframe",
	"//sys/src/libgeometry:libgeometry",
	"//sys/src/libhttpd:libhttpd",
	"//sys/src/libbin:libbin",
	"//sys/src/liblex:liblex",
	"//sys/src/libmemdraw:libmemdrawiprint",
	"//sys/src/libmemlayer:libmemlayer",
	"//sys/src/libmemdraw:libmemdraw",
	"//sys/src/libdraw:libdraw",
	"//sys/src/libplumb:libplumb",
	"//sys/src/libregexp:libregexp",
	"//sys/src/libstdio:libstdio",
	"//sys/src/libString:libString",
	"//sys/src/liboventi:liboventi",
	"//sys/src/lib9p:lib9p",
	"//sys/src/libauth:libauth",
	"//sys/src/libauthsrv:libauthsrv",
	"//sys/src/libndb:libndb",
	"//sys/src/libip:libip",
	"//sys/src/libventi:libventi",
	"//sys/src/libsec:libsec",
	"//sys/src/libmp:libmp",
	"//sys/src/libthread:libthread",
	"//sys/src/libmach:libmach",
	"//sys/src/libbio:libbio",
	"//sys/src/libc:libc",
]

CMD_LINK_OPTS = [
	"-static",
	"-e_main",
]

KLIB_COMPILER_FLAGS = [
	"-mcmodel=kernel",
	"-O0",
	"-mno-red-zone",
	"-ffreestanding",
	"-fno-builtin",
	"-Wall",
	"-Wno-missing-braces",
	"-Wno-parentheses",
	"-Wno-unknown-pragmas",
	"-Wuninitialized",
	"-g",
]

LIB_COMPILER_FLAGS = [
	"-std=c11",
	"-fasm",
	"-c",
	"-ffreestanding",
	"-fno-builtin",
	"-fno-omit-frame-pointer",
	"-g",
	"-gdwarf-2",
	"-ggdb",
	"-mcmodel=small",
	"-mno-red-zone",
	"-O0",
	"-static",
	"-Wall",
	"-Wno-missing-braces",
	"-Wno-parentheses",
	"-Wno-unknown-pragmas"
]


harvey_binary = cc_binary(
	copts=LIB_COMPILER_FLAGS,
	includes=[
		"//sys/include",
		"//amd64/include",
	],
	deps=CMD_DEPS,
	strip=true,
	linkopts=CMD_LINK_OPTS
)
