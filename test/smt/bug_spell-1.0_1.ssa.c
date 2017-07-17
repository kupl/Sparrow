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
  int pos1, pos2, pos3 ;

  tmp = malloc((size_t )(str->len + 1));
  nstr = (char *)tmp;
  pos1 = 0;
  if (! str) {
    return (nstr);
  } else
  if (! str->str) {
    return (nstr);
  }
  {
  while (1) {
    pos2 = phi (pos1, pos3);
    while_continue: /* CIL Label */ ;
    if (! (pos2 < str->len)) {
      goto while_break;
    }
    sparrow_print (pos2);
//    if (! *(str->str + pos2)) {
//      *(str->str + pos2) = (char )' ';
//    }
//    *(nstr + pos2) = *(str->str + pos2);
    pos3 = pos2 + 1;
  }
  while_break: /* CIL Label */ ;
  }
  *(nstr + (pos2 + 1)) = (char)0; // true bug: 'pos+1' should be just 'pos'
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
