/* insertion sort ascending order */
#include <limits.h>
#include <stdio.h>

int main()
{
    int n, array[1000], c, d, t ;

    printf("Enter a number of elements\n") ;
    scanf("%d", &n) ;
    /*@ assert rte: initialization: \initialized(&n); */
    printf("Enter %d integers\n", n) ;

    /*@requires n < 1000; */
    /*@assert n >= INT_MIN;  */
    /*@assert n <= INT_MAX; */
    
    /*@ loop invariant c >= 0 && c <= n;
	 @ loop assigns c;
	*/
    for (c = 0; c < n; c++)
    {
	/*@assert c < n;*/
	/*@ assert rte: initialization: \initialized(&c); */
        scanf("%d", &array[c]) ;
	/*@assert array[c] >= INT_MIN;  */
	/*@assert array[c] <= INT_MAX; */
    }
    /*@assert c == n;*/
    /*@ loop invariant c >= 1 && c <= n;
	 @ loop assigns c,d,t;
	*/
    for (c = 1; c <= n - 1; c++)
    {
	/*@assert c <= n-1;*/
        d = c ;

     /*@ loop invariant d <= c && d >= 0 || array[d] < array[d - 1];
	 @ loop assigns d,t;
	*/
        while (d > 0
            && array[d] < array[d - 1])
        {
            t = array[d] ;

	    /*@assert t == array[d]; */
            array[d] = array[d - 1] ;

	    /*@assert array[d-1] == array[d]; */
            array[d - 1] = t ;

            /*@assert t == array[d-1]; */
            /*@assert array[d-1] <= array[d]; */
            d-- ;
        }
    }

    /*@assert c == n;*/
    printf("Sorted list in ascending order:\n");

    /*@ loop invariant c >= 0 && c <= n-1;
	 @ loop assigns c;
	*/
    for (c = 0; c <= n - 1; c++)
    {
        printf("%d\n", array[c]) ;
    }

    return 0 ;
}
