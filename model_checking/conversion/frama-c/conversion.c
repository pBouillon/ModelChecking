#include <stdio.h>

int main()
{
    int n, c, k ;

    printf("Enter an integer in decimal number system\n") ;
    scanf("%d", &n);

    printf("%d in binary number system is:\n", n) ;
    
    /*@ loop invariant c >= -1 && c <= 31;
    @ loop assigns c;
    */	
    for (c = 31; c >= 0; c--)
    {
	/*@assert c >= 0; */;
        k = n >> c ;

	/*@assert k == n >> c; */;
        if (k & 1)
        {
            printf ("1") ;
        }
        else
        {
            printf("0") ;
        }
    }

    printf("\n") ;

    return 0 ;
}
