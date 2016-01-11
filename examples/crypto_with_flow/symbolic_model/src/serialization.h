#ifndef SERIALIZATION_H
#define SERIALIZATION_H

#include "invariants.h"
#include "general.h"
#include "item_constraints.h"

/*@
  
lemma void serialize_item(item i);
  requires proof_obligations(?pub) &*&
           [_]item_constraints(i, ?cs, pub) &*&
           [_]pub(i);
  ensures  proof_obligations(pub) &*& 
           [_]public_generated(polarssl_pub(pub))(cs);

@*/

int serialize_to_public_message(char** dest, struct item* item);
  /*@ requires [?f0]world(?pub) &*& 
               [?f1]item(item, ?i, pub) &*& pointer(dest, _) &*& 
               [_]pub(i); @*/
  /*@ ensures  [f0]world(pub) &*& 
               [f1]item(item, i, pub) &*& pointer(dest, ?d) &*& 
               malloc_block(d, result) &*& result > 1 &*&
               chars(d, result, ?cs) &*&
               [_]item_constraints(i, cs, pub); @*/

#endif