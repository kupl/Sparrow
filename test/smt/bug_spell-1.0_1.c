typedef unsigned int size_t;
struct str {
   char *str ;
   int len ;
   size_t mem ;
};
typedef struct str str_t;

int str_to_nstr(str_t *str) 
{
  char *nstr ;
  void *tmp ;
  int pos ;

  tmp = malloc((size_t )(str->len + 1));
  nstr = (char *)tmp;
  pos = 0;
  if (! str) {
    return (nstr);
  } else
  if (! str->str) {
    return (nstr);
  }
  {
  while (1) {
    while_continue: /* CIL Label */ ;
    sparrow_print (pos);
    if (! (pos < str->len)) {
      goto while_break;
    }
    sparrow_print (pos);
//    if (! *(str->str + pos)) {
//      *(str->str + pos) = (char )' ';
//    }
//    *(nstr + pos) = *(str->str + pos);
    pos ++;
  }
  while_break: /* CIL Label */ ;
  }
  *(nstr + (pos + 1)) = (char)0; // true bug: 'pos+1' should be just 'pos'
  return (nstr);
}

int main()
{
  str_t* str = (str_t*)malloc((size_t)sizeof(*str));
  str->mem = unknown();
  str->str = (char*)malloc(unknown());
  str->len = unknown();
  str_to_nstr (str);
}
