
/*@
  lemma void smart(list<int> l);
  requires true;
  ensures length(l) < 3;
  @*/

void to_verify()
//@ requires true;
//@ ensures true;
{
  //@ list<int> a = cons(1, cons(2, cons(3, nil)));
  //@ assert length(a) < 3;
}
