#include <limits.h>
#include <stdio.h>
#include <math.h>

int power(int,int);

/*@ensures \result == 0;*/
int main()
{
	int n, sum = 0, temp, remainder, digits = 0;
	
	/*@ assert sum == 0; */
	/*@ assert digits == 0;*/
	printf("Input an integer\n");
	scanf("%d", &n);
	
	temp = n;

	//Count number of digits
	
	/*@ loop invariant temp >= 0 && temp <= n;
	 @ loop assigns temp, digits;
	*/
	while(temp != 0){
	/*@ assert temp != 0;*/
		digits++;
		temp = temp/10;
	}
	
	/*@ assert temp == 0;*/
	temp = n;

	/*@ loop invariant temp >= 0 && temp <= n;
	 @ loop assigns temp, remainder, sum;
	*/
	while ( temp != 0){
		/*@ assert temp != 0;*/
		remainder = temp%10;

		/*@assert remainder == temp % 10;*/
		sum = sum + power(remainder, digits);
		temp = temp/10;
	}
	
	if(n == sum){
		/*@ assert temp == 0; */
		printf("%d is an Armstrong number.\n",n);
	}
	else{
		/*@ assert temp == 0; */
		printf("%d is not an Armstrong number.\n",n);
	}
	return 0;
}


/*@     requires n >= 0;
	requires r >= 0;
	requires n <= INT_MAX;
	requires r <= INT_MAX;
	ensures \result >= 0;
 
*/
int power(int n, int r){
	int c, p = 1;
	/*@assert p == 1;*/ 
	/*@ loop invariant c >= 1 && c <= r+1;
	 @ loop assigns c,p;
	*/
	for (c =1; c <=r; c++){
		/*@assert c <= r;*/
		p = p*n;
		/*@ assert p == \pow(n, c);*/
	}

	return p;
}
