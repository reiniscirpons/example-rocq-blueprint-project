Require Import ssreflect ssrbool ssrfun.

Section MyNaturals.

Inductive MyNat: Type := 
| zero: MyNat
| succ: MyNat -> MyNat.

Definition one := succ zero.
Definition two := succ one.

End MyNaturals.
