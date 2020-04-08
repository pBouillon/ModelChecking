#include "errno.h"
#include "math.h"
#include "stdarg.h"
#include "stddef.h"
#include "stdio.h"
int power(int n, int r);

/*@ requires valid_read_string(format);
    assigns \result, __fc_stdout->__fc_FILE_data;
    assigns \result
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..)));
    assigns __fc_stdout->__fc_FILE_data
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..)));
 */
int printf_va_1(char const * __restrict format);

/*@ requires valid_read_string(format);
    requires \valid(param0);
    ensures \initialized(param0);
    assigns \result, __fc_stdin->__fc_FILE_data, *param0;
    assigns \result
      \from (indirect: __fc_stdin->__fc_FILE_id), __fc_stdin->__fc_FILE_data,
            (indirect: *(format + (0 ..)));
    assigns __fc_stdin->__fc_FILE_data
      \from (indirect: __fc_stdin->__fc_FILE_id), __fc_stdin->__fc_FILE_data,
            (indirect: *(format + (0 ..)));
    assigns *param0
      \from (indirect: __fc_stdin->__fc_FILE_id), __fc_stdin->__fc_FILE_data,
            (indirect: *(format + (0 ..)));
 */
int scanf_va_1(char const * __restrict format, int *param0);

/*@ requires valid_read_string(format);
    assigns \result, __fc_stdout->__fc_FILE_data;
    assigns \result
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..))),
            param0;
    assigns __fc_stdout->__fc_FILE_data
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..))),
            param0;
 */
int printf_va_2(char const * __restrict format, int param0);

/*@ requires valid_read_string(format);
    assigns \result, __fc_stdout->__fc_FILE_data;
    assigns \result
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..))),
            param0;
    assigns __fc_stdout->__fc_FILE_data
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..))),
            param0;
 */
int printf_va_3(char const * __restrict format, int param0);

/*@ ensures \result ≡ 0; */
int main(void)
{
  int __retres;
  int n;
  int temp;
  int remainder_0;
  int sum = 0;
  int digits = 0;
  /*@ assert sum ≡ 0; */ ;
  /*@ assert digits ≡ 0; */ ;
  printf_va_1("Input an integer\n");
  scanf_va_1("%d",& n);
  temp = n;
  /*@ loop invariant temp ≥ 0 ∧ temp ≤ n;
      loop assigns temp, digits; */
  while (temp != 0) {
    /*@ assert temp ≢ 0; */ ;
    /*@ assert rte: signed_overflow: digits + 1 ≤ 2147483647; */
    digits ++;
    temp /= 10;
  }
  /*@ assert temp ≡ 0; */ ;
  temp = n;
  /*@ loop invariant temp ≥ 0 ∧ temp ≤ n;
      loop assigns temp, remainder_0, sum;
  */
  while (temp != 0) {
    int tmp;
    /*@ assert temp ≢ 0; */ ;
    remainder_0 = temp % 10;
    /*@ assert remainder_0 ≡ temp % 10; */ ;
    tmp = power(remainder_0,digits);
    /*@ assert rte: signed_overflow: -2147483648 ≤ sum + tmp; */
    /*@ assert rte: signed_overflow: sum + tmp ≤ 2147483647; */
    sum += tmp;
    temp /= 10;
  }
  if (n == sum) {
    /*@ assert temp ≡ 0; */ ;
    printf_va_2("%d is an Armstrong number.\n",n);
  }
  else {
    /*@ assert temp ≡ 0; */ ;
    printf_va_3("%d is not an Armstrong number.\n",n);
  }
  __retres = 0;
  return __retres;
}

/*@ requires n ≥ 0;
    requires r ≥ 0;
    requires n ≤ 2147483647;
    requires r ≤ 2147483647;
    ensures \result ≥ 0;
 */
int power(int n, int r)
{
  int c;
  int p = 1;
  /*@ assert p ≡ 1; */ ;
  c = 1;
  /*@ loop invariant c ≥ 1 ∧ c ≤ r + 1;
      loop assigns c, p; */
  while (c <= r) {
    /*@ assert c ≤ r; */ ;
    /*@ assert rte: signed_overflow: -2147483648 ≤ p * n; */
    /*@ assert rte: signed_overflow: p * n ≤ 2147483647; */
    p *= n;
    /*@ assert p ≡ \pow(n, c); */ ;
    /*@ assert rte: signed_overflow: c + 1 ≤ 2147483647; */
    c ++;
  }
  return p;
}


