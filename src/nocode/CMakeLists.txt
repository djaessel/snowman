set(SOURCES
    main.cpp
)

add_executable(nocode ${SOURCES})
target_link_libraries(nocode nc classner ${Boost_LIBRARIES} ${NC_QT_CORE})

set_property(TARGET nocode PROPERTY CXX_STANDARD 17)
set_property(TARGET nocode PROPERTY CXX_STANDARD_REQUIRED ON)

if (NOT ${IDA_PLUGIN_ENABLED})
    install(TARGETS nocode RUNTIME DESTINATION bin)
    if(WIN32 AND NOT ${NC_QT5})
        install_qt4_executable("bin/nocode.exe")
    endif()
endif()

# vim:set et sts=4 sw=4 nospell:
