
set(SOURCES
    classner.cpp
    classner.h
    classreader.cpp
    classreader.h
    classstorer.cpp
    classstorer.h
    fixedclass.cpp
    fixedclass.h
    fixedfunction.cpp
    fixedfunction.h
    functionanalyzer.cpp
    functionanalyzer.h
    rawclass.cpp
    rawclass.h
    rawfunction.cpp
    rawfunction.h
    reinterpretalter.cpp
    reinterpretalter.h
    specialvals.cpp
    specialvals.h
    structer.cpp
    structer.h
    classanalyzer.cpp
    classanalyzer.h
    gotogo.cpp
    gotogo.h
)


find_package(Qt5Core REQUIRED)
# find_package(Qt5Widgets REQUIRED)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

qt4_wrap_cpp(SOURCES OPTIONS -DQ_MOC_RUN)

add_library(classner STATIC ${SOURCES})

set_property(TARGET classner PROPERTY CXX_STANDARD 17)
set_property(TARGET classner PROPERTY CXX_STANDARD_REQUIRED ON)

target_link_libraries(classner Qt5::Core)

