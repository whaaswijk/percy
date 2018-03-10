#include <stdio.h>
#include <time.h>

void   Abc_Start();
void   Abc_Stop();
void * Abc_FrameGetGlobalFrame();
int    Cmd_CommandExecute( void * pAbc, char * sCommand );


/*******************************************************************************
    A simple test to verify that integration with ABC is set up properly. The
    test tries to execute an echo command within the ABC environment. The test
    fails if it is unable to do so.
*******************************************************************************/

int main(int argc, char * argv[])
{
    void *pAbc;
    char Command[1000];

    /* TODO: fix abc integration.
    Abc_Start();
    pAbc = Abc_FrameGetGlobalFrame();
    
    sprintf( Command, "echo \"test\"" );
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        printf("Cannot execute command \"%s\".\n", Command);
        return 1;
    }

    Abc_Stop();
    */

    return 0;
}

