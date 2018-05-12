#include <stdio.h>
#include <time.h>

#include <base/main/main.h>

/*******************************************************************************
    A simple test to verify that integration with ABC is set up properly. The
    test tries to execute an echo command within the ABC environment. The test
    fails if it is unable to do so.
*******************************************************************************/
int 
main(int argc, char * argv[])
{
    char Command[1000];

    abc::Abc_Start();
    auto pAbc = abc::Abc_FrameGetGlobalFrame();
    
    sprintf( Command, "echo \"test\"" );
    if ( abc::Cmd_CommandExecute( pAbc, Command ) )
    {
        printf("Cannot execute command \"%s\".\n", Command);
        return 1;
    }

    abc::Abc_Stop();

    return 0;
}

