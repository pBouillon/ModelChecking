#include "errno.h"
#include "stdarg.h"
#include "stddef.h"
#include "stdio.h"
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
int scanf_va_2(char const * __restrict format, int *param0);

/*@ requires valid_read_string(format);
    assigns \result, __fc_stdout->__fc_FILE_data;
    assigns \result
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..)));
    assigns __fc_stdout->__fc_FILE_data
      \from (indirect: __fc_stdout->__fc_FILE_id),
            __fc_stdout->__fc_FILE_data, (indirect: *(format + (0 ..)));
 */
int printf_va_3(char const * __restrict format);

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
int printf_va_4(char const * __restrict format, int param0);

int main(void)
{
  int __retres;
  int n;
  int array[1000];
  int c;
  int d;
  int t;
  printf_va_1("Enter a number of elements\n");
  scanf_va_1("%d",& n);
  /*@ assert rte: initialization: \initialized(&n); */ ;
  printf_va_2("Enter %d integers\n",n);
  /*@ requires n < 1000; */
  /*@ assert n ≥ -2147483647 - 1; */
  /*@ assert n ≤ 2147483647; */
  c = 0;
  /*@ loop invariant c ≥ 0 ∧ c ≤ n;
      loop assigns c; */
  while (c < n) {
    /*@ assert c < n; */ ;
    /*@ assert rte: initialization: \initialized(&c); */ ;
    scanf_va_2("%d",& array[c]);
    /*@ assert array[c] ≥ -2147483647 - 1; */ ;
    /*@ assert array[c] ≤ 2147483647; */ ;
    /*@ assert rte: signed_overflow: c + 1 ≤ 2147483647; */
    c ++;
  }
  /*@ assert c ≡ n; */ ;
  c = 1;
  /*@ loop invariant c ≥ 1 ∧ c ≤ n;
      loop assigns c, d, t; */
  while (1) {
    /*@ assert rte: signed_overflow: -2147483648 ≤ n - 1; */
    if (! (c <= n - 1)) break;
    /*@ assert c ≤ n - 1; */ ;
    d = c;
    /*@ loop invariant (d ≤ c ∧ d ≥ 0) ∨ array[d] < array[d - 1];
        loop assigns d, t;
    */
    while (1) {
      if (d > 0) {
        /*@ assert rte: index_bound: 0 ≤ d; */
        /*@ assert rte: index_bound: d < 1000; */
        /*@ assert rte: signed_overflow: -2147483648 ≤ d - 1; */
        /*@ assert rte: index_bound: 0 ≤ (int)(d - 1); */
        /*@ assert rte: index_bound: (int)(d - 1) < 1000; */
        if (! (array[d] < array[d - 1])) break;
      }
      else break;
      /*@ assert rte: index_bound: 0 ≤ d; */
      /*@ assert rte: index_bound: d < 1000; */
      t = array[d];
      /*@ assert t ≡ array[d]; */ ;
      /*@ assert rte: index_bound: 0 ≤ d; */
      /*@ assert rte: index_bound: d < 1000; */
      /*@ assert rte: signed_overflow: -2147483648 ≤ d - 1; */
      /*@ assert rte: index_bound: 0 ≤ (int)(d - 1); */
      /*@ assert rte: index_bound: (int)(d - 1) < 1000; */
      array[d] = array[d - 1];
      /*@ assert array[d - 1] ≡ array[d]; */ ;
      /*@ assert rte: index_bound: 0 ≤ (int)(d - 1); */
      /*@ assert rte: index_bound: (int)(d - 1) < 1000; */
      /*@ assert rte: signed_overflow: -2147483648 ≤ d - 1; */
      array[d - 1] = t;
      /*@ assert t ≡ array[d - 1]; */ ;
      /*@ assert array[d - 1] ≤ array[d]; */ ;
      /*@ assert rte: signed_overflow: -2147483648 ≤ d - 1; */
      d --;
    }
    /*@ assert rte: signed_overflow: c + 1 ≤ 2147483647; */
    c ++;
  }
  /*@ assert c ≡ n; */ ;
  printf_va_3("Sorted list in ascending order:\n");
  c = 0;
  /*@ loop invariant c ≥ 0 ∧ c ≤ n - 1;
      loop assigns c; */
  while (1) {
    /*@ assert rte: signed_overflow: -2147483648 ≤ n - 1; */
    if (! (c <= n - 1)) break;
    /*@ assert rte: index_bound: 0 ≤ c; */
    /*@ assert rte: index_bound: c < 1000; */
    printf_va_4("%d\n",array[c]);
    /*@ assert rte: signed_overflow: c + 1 ≤ 2147483647; */
    c ++;
  }
  __retres = 0;
  return __retres;
}


