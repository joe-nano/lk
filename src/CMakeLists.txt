#####################################################################################################################
#
# Project Sources
#
#####################################################################################################################

set(LK_SRC
        absyn.cpp
        eval.cpp
        parse.cpp
        vm.cpp
        codegen.cpp
        invoke.cpp
        env.cpp
        lex.cpp
        sqlite3.c
        stdlib.cpp)


#####################################################################################################################
#
# CMake Targets
#
#####################################################################################################################

# lk library
add_library(lk STATIC ${LK_SRC})
set_target_properties(lk
        PROPERTIES
        DEBUG_POSTFIX "d"
        PREFIX ""
        )
if (MSVC)
    set_target_properties(lk
            PROPERTIES
            LINK_FLAGS /SUBSYSTEM:CONSOLE)
endif ()

target_include_directories(lk PRIVATE ../include)


#####################################################################################################################
#
# Link Libraries and Options
#
#####################################################################################################################

# lk library
if (${CMAKE_PROJECT_NAME} STREQUAL export_config)
    target_compile_definitions(lk PUBLIC _export_config_)
endif ()

