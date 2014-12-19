#include "my_string.h"
#include <stdio.h>
#include <string.h>
#include "axiomatique.h"


/*
  Return the number of caracters in the string (final zero excluded). 
*/
/*@ requires \valid(str+ (0 .. strlen_(str))); 
  @ ensures \result == strlen_(str);
  @ assigns \nothing;
  @*/
int my_strlen(const char *str){
  int i = 0;

  /*@ loop invariant str[i] == 0 ==> i == strlen_(str);
    @ loop invariant 0 <= i <= strlen_(str);
    @ loop assigns i;
    @ loop variant strlen_(str) - i;
    @*/
  while(str[i]!='\0'){
    i++;
  }

  return i;
} 

/*
  Will copy length bytes starting at src+start in position  at dst

*/
/*@ requires length > 0;
  @ requires start >= 0;
  @ requires start+length <= strlen_(src);
  @ requires \valid(dst+(0..length));
  @ requires \valid(src+(start..start+length)-1);
  @ requires \separated(dst+(0..length), (src+(start..start+length-1)));
  @ assigns dst[0..length];
  @ ensures \forall integer jj;  0 <= jj < length ==> \at(dst[jj],Post)==\at(src[start+jj],Pre) ;
  @ ensures \at(dst[length],Post)=='\0' ;
  @*/
void strsubstring(char *dst, const char *src, int start, int length){

    int i;
    /*@ loop assigns i,dst[0..length-1];     
      @ loop invariant equality : \forall integer jj; 0 <= jj < i ==> dst[jj]==\at(src[start+jj],Pre);
      @ loop invariant 0 <= i <= length;
      @ loop variant length - i;
      @ */
    for(i=0;i<length;i++){
	dst[i]=src[start+i];
    }
    /*@assert i==length;*/
    dst[length]='\0';
}
/*
/* @ requires n > 0;
  @ requires \valid(t+(0..(n-1)));
  @ assigns t[0..n-1];
  @ ensures \forall integer j;  0 <= j <  n ==> t[j] == x ;
  @* /
void fill(int* t, int n, int x) {
    int i;
    /* @ loop assigns i,t[0..(i-1)];     
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer j; 0 <= j < i ==> t[j] == x;
      @ loop variant n - i;
      @ * /
  for (i = 0; i < n; i++)
    t[i] = x;

   return;
}
*/
/*@ requires \valid(dst+(0..(strlen_(dst)+strlen_(src))));
  @ requires \valid(src+(0..strlen_(src)));
  @ ensures \forall integer j; 0<= j < strlen_(dst) ==> \at(dst[j],Old) == \at(dst[j],Pre);
  @ ensures \forall integer j; strlen_(dst) <= j <= strlen_(dst)+strlen_(src) ==> \at(dst[j],Old) == \old(src[j]);
@*/
void strappend(char *dst, const char *src){
//  strsubstring(dst+my_strlen(dst),src,0,my_strlen(src));
}
/*
int main(int argc, char *argv[])
{
  const char* str="Test string";
  char src[80]={'\0'};
  strncpy(src,str,my_strlen(str));
  printf ("%d|%s|\n",my_strlen(str),src);

  {
    char dst[80]={'\0'}; 
    strsubstring(dst,src,0,my_strlen(src)-5);
    printf ("|%s|\n",dst);
  }
  {
    char dst[80]={'\0'}; 
    const char* str2 = "My Pipo";
    strncpy(dst,str,my_strlen(str));
    strappend(dst,str2);
    printf ("|%s|\n",dst);
  }
  return 0;
}
*/
