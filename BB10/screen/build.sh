#!/bin/sh
# Build the C++ tools next to the Python scripts in src/ (where the scripts look for them).
#   ./build.sh            uses g++ (override with CXX=..., CXXFLAGS=...)
set -e
cd "$(dirname "$0")/src"
CXX=${CXX:-g++}
CXXFLAGS=${CXXFLAGS:--O2 -std=c++17}
EXE=
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) EXE=.exe; LDFLAGS=${LDFLAGS:--static} ;;   # static: no runtime DLLs needed
esac
for t in renum stage35 stage35g hyb10; do
  echo "$CXX $CXXFLAGS -o $t$EXE $t.cpp $LDFLAGS"
  $CXX $CXXFLAGS -o "$t$EXE" "$t.cpp" $LDFLAGS
done
