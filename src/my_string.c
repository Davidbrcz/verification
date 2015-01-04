#include "my_string.h"
#include <stdio.h>
#include <string.h>
#include "axiomatique.h"

/*
  Return the number of caracters in the string (final zero excluded). 
*/
/*@ requires \valid(str+ (0 .. strlen_(str))); 
  @ ensures \result == strlen_(str);
  @ ensures \result >= 0;
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
  Will copy length bytes starting at src+start in position at dst
  and add the zero terminator at dst[length]
*/
/*@ requires length >= 0;
  @ requires start >= 0;
  @ requires start+length <= strlen_(src);
  @ requires \valid(dst+(0..length));
  @ requires \valid(src+(start..start+length-1));
  @ requires \separated(dst+(0..length), (src+(start..start+length-1)));
  @ assigns dst[0..length];
  @ ensures copie :  \forall integer jj;  0 <= jj < length ==> \at(dst[jj],Post)==\at(src[start+jj],Pre) ;
  @ ensures zero_terminated : \at(dst[length],Post)=='\0' ;
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

/*@ requires \valid(dst+(0..(strlen_{Pre}(dst)+strlen_{Pre}(src))));
  @ requires \valid(src+(0..strlen_{Pre}(src)));
  @ requires \separated(dst+(0..strlen_{Pre}(dst)+strlen_{Pre}(src)),src+(0..strlen_{Pre}(src)-1));
  @ assigns dst[strlen_(dst)..strlen_(dst)+strlen_(src)];
  @ ensures debut_constant : \forall integer j; 0<= j < \old(strlen_(dst)) ==> \at(dst[j],Old) == \at(dst[j],Post);
  @ ensures suite_copiee : \forall integer j; 0 <= j < \old(strlen_(src)) ==> dst[j+\old(strlen_(dst))] == \at(src[j],Old);
  @ ensures zero_final : dst[strlen_(dst)] == '\0' ;
  @*/
void strappend(char *dst, const char *src){
    strsubstring(dst+my_strlen(dst),src,0,my_strlen(src));
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
  printf("-------------------\n");
  {
    char dst[80]={'\0'}; 
    const char* str2 = "My Pipo";
    strncpy(dst,str,my_strlen(str));
    strappend2(dst,str2);
    printf ("|%s|\n",dst);
  }
  return 0;
}*/

