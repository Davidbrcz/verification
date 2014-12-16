#include "my_string.h"
#include <stdio.h>
#include <string.h>
#include "axiomatique.h"

/*@ requires \valid(str+ (0 .. strlen_(str))); 
  @ ensures \result == strlen_(str);
  @ assigns \nothing;
  @*/
int my_strlen(const char *str){
  int i = 0;
  /*@ assert i == 0; */

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
  @ Demanque dst(start+lengh+1) == 0
  @ Demande que dst(0..length) soit valide
  @ Demande que dst(start..start+length) soit valide
  @ Demanque que start+length < strlen_(src)
  @ Assurer que pour tout i entre 0 et length dst(i) == src[start+i]
  @ Ne change src
@*/
void strsubstring(char *dst, const char *src, int start, int length){
  int i = 0;
  /*@assert i == 0;@*/

  /* loop
    @ variant length - i;
    @ invariant 
    @ */
  for(;i<length;i++){
    dst[i]=src[start+i];
  }
}

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
