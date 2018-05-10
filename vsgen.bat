ECHO Generating Visual Studio solution in build/ folder 
mkdir build 2> nul
cd build
cmake -G "Visual Studio 15 2017" ..
cd ..
