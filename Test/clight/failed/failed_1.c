#include <stdio.h>
int main()
{
	// Fatal error: glibc detected an invalid stdio handle
    // Aborted (core dumped)
	putc_unlocked('\n', stdout);
	return 0;
}
