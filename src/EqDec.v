Require Export EquivDec.
Require Import Strings.String.

Coercion is_left A B (u : {A} + {B}) := if u then true else false.

Global Instance string_eqdec : EqDec string eq := string_dec.
