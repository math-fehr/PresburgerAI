Require Export ZArith Strings.String.
From PresburgerAI Require Import RelationalAbstractDomain Imp PartialMap TransferFunction Utils.

Open Scope Z_scope.

(** Affine expressions **)
Axiom Aff : nat -> Type.
Axiom eval_aff : forall {n}, Aff n -> Array Z n -> Z.

(** A constant affine expression **)
Axiom aff_const : forall n, Z -> Aff n.
Axiom eval_aff_const : forall n c p, eval_aff (aff_const n c) p = c.

(** An affine expression equal to the value of an input variable **)
Axiom aff_var : forall {n}, Fin n -> Aff n.
Axiom eval_aff_var : forall n c (p: Array Z n), eval_aff (aff_var c) p = array_get p c.

(** The addition of two affine expressions **)
Axiom aff_plus : forall {n}, Aff n -> Aff n -> Aff n.
Axiom eval_aff_plus :
  forall n a1 a2 (p: Array Z n), eval_aff (aff_plus a1 a2) p = (eval_aff a1 p) + (eval_aff a2 p).

(** The multiplication of an affine expression with a constant **)
Axiom aff_mul : forall {n}, Z -> Aff n -> Aff n.
Axiom eval_aff_mul : forall n c a (p: Array Z n), eval_aff (aff_mul c a) p = c * eval_aff a p.



(** Presburger sets **)
Axiom PSet : nat -> Type.
Axiom eval_pset : forall {n}, PSet n -> Array Z n -> bool.

(** Empty set **)
Axiom empty_pset : forall n, PSet n.
Axiom eval_empty_pset : forall n p, eval_pset (empty_pset n) p = false.

(** Universe set **)
Axiom universe_pset : forall n, PSet n.
Axiom eval_universe_pset : forall n p, eval_pset (universe_pset n) p = true.

(** The union of two sets **)
Axiom union_pset : forall {n}, PSet n -> PSet n -> PSet n.
Axiom eval_union_pset :
  forall n s1 s2 (p: Array Z n), eval_pset (union_pset s1 s2) p = orb (eval_pset s1 p) (eval_pset s2 p).

(** The intersection of two sets **)
Axiom intersect_pset : forall {n}, PSet n -> PSet n -> PSet n.
Axiom eval_intersect_pset :
  forall n s1 s2 (p: Array Z n), eval_pset (intersect_pset s1 s2) p = andb (eval_pset s1 p) (eval_pset s2 p).

(** The subtraction of one set by another **)
Axiom subtract_pset : forall {n}, PSet n -> PSet n -> PSet n.
Axiom eval_subtract_pset :
  forall n s1 s2 (p: Array Z n), eval_pset (subtract_pset s1 s2) p = andb (eval_pset s1 p) (negb (eval_pset s2 p)).


(** Piecewise affine expression **)
Axiom PwAff : nat -> Type.
Axiom eval_pwaff : forall {n}, PwAff n -> Array Z n -> option Z.

(** A piecewise affine expression from an affine expression **)
Axiom pwaff_from_aff : forall {n}, Aff n -> PwAff n.
Axiom eval_pwaff_from_aff : forall n (a: Aff n) p,
    eval_pwaff (pwaff_from_aff a) p = Some (eval_aff a p).

(** Intersect the domain of a piecewise affine expression with a set **)
Axiom intersect_domain_pwaff : forall {n}, PwAff n -> PSet n -> PwAff n.
Axiom eval_pwaff_intersect_domain : forall n (pa: PwAff n) s p,
    eval_pwaff (intersect_domain_pwaff pa s) p =
    if eval_pset s p then
      eval_pwaff pa p
    else
      None.

(** Maximum of two piecewise affine expressions **)
Axiom max_pwaff : forall {n}, PwAff n -> PwAff n -> PwAff n.
Axiom eval_max_pwaff :
  forall n (pa1 pa2: PwAff n) p,
    eval_pwaff (max_pwaff pa1 pa2) p =
    match eval_pwaff pa1 p, eval_pwaff pa2 p with
    | None, v2 => v2
    | Some v1, None => Some v1
    | Some v1, Some v2 => Some (Z.max v1 v2)
    end.

(** The set where both piecewise affine expressions are defined and equal **)
Axiom eq_set_pwaff : forall {n}, PwAff n -> PwAff n -> PSet n.
Axiom eval_eq_set_pwaff : forall n (p1 p2: PwAff n) p,
    eval_pset (eq_set_pwaff p1 p2) p =
    match eval_pwaff p1 p, eval_pwaff p2 p with
    | Some v1, Some v2 => v1 ==b v2
    | _, _ => false
    end.

(** The set where both piecewise affine expressions are defined and equal **)
Axiom ne_set_pwaff : forall {n}, PwAff n -> PwAff n -> PSet n.
Axiom eval_ne_set_pwaff : forall n (p1 p2: PwAff n) p,
    eval_pset (ne_set_pwaff p1 p2) p =
    match eval_pwaff p1 p, eval_pwaff p2 p with
    | Some v1, Some v2 => v1 <>b v2
    | _, _ => false
    end.

(** Presburger maps **)
Axiom PMap : nat -> nat -> Type.
Axiom eval_pmap : forall {n m}, PMap n m -> Array Z n -> Array Z m -> bool.

(** Empty map **)
Axiom empty_pmap : forall n m, PMap n m.
Axiom eval_empty_pmap : forall n m p1 p2, eval_pmap (empty_pmap n m) p1 p2 = false.

(** Universe map **)
Axiom universe_pmap : forall n m, PMap n m.
Axiom eval_universe_pmap : forall n m p1 p2, eval_pmap (universe_pmap n m) p1 p2 = true.

(** Identity map **)
Axiom id_pmap : forall n, PMap n n.
Axiom eval_id_pmap :
  forall n p1 p2, eval_pmap (id_pmap n) p1 p2 = true <-> p1 = p2.

(** Union of two maps **)
Axiom union_pmap : forall {n m}, PMap n m -> PMap n m -> PMap n m.
Axiom eval_union_pmap :
  forall n m (m1 m2: PMap n m) p1 p2,
    eval_pmap (union_pmap m1 m2) p1 p2 =
    orb (eval_pmap m1 p1 p2) (eval_pmap m2 p1 p2).

(** Intersection of two maps **)
Axiom intersect_pmap : forall {n m}, PMap n m -> PMap n m -> PMap n m.
Axiom eval_intersect_pmap :
  forall n m (m1 m2: PMap n m) p1 p2,
    eval_pmap (union_pmap m1 m2) p1 p2 =
    andb (eval_pmap m1 p1 p2) (eval_pmap m2 p1 p2).

(** Intersection of two maps **)
Axiom intersect_domain_pmap : forall {n m}, PMap n m -> PSet n -> PMap n m.
Axiom eval_intersect_domain_pmap :
  forall n1 n2 (m: PMap n1 n2) s p1 p2,
    eval_pmap (intersect_domain_pmap m s) p1 p2 =
    andb (eval_pmap m p1 p2) (eval_pset s p1).

(** Intersection of two maps **)
Axiom intersect_range_pmap : forall {n m}, PMap n m -> PSet m -> PMap n m.
Axiom eval_intersect_range_pmap :
  forall n1 n2 (m: PMap n1 n2) s p1 p2,
    eval_pmap (intersect_range_pmap m s) p1 p2 =
    andb (eval_pmap m p1 p2) (eval_pset s p2).

(** Functional composition of two maps **)
Axiom compose_pmap : forall {n1 n2 n3}, PMap n1 n2 -> PMap n2 n3 -> PMap n1 n3.
Axiom eval_compose_pmap :
  forall n1 n2 n3 (m1: PMap n1 n2) (m2: PMap n2 n3) p1 p3,
    eval_pmap (compose_pmap m1 m2) p1 p3 = true <->
    exists p2, eval_pmap m1 p1 p2 = true /\ eval_pmap m2 p2 p3 = true.

(** Transitive closure of a map **)
Axiom transitive_closure_pmap : forall {n}, PMap n n -> PMap n n.
Axiom eval_transitive_closure_pmap :
  forall n (m: PMap n n) p1 p2,
    transitive_closure (fun p => eval_pmap m (fst p) (snd p) = true) (p1, p2) ->
    eval_pmap (transitive_closure_pmap m) p1 p2 = true.

Axiom pmap_project_out_out_dim : forall {n1 n2}, PMap n1 n2 -> Fin n2 -> PMap n1 n2.
Axiom eval_pmap_project_out_out_dim : forall n1 n2 (m: PMap n1 n2) i p1 p2,
    eval_pmap (pmap_project_out_out_dim m i) p1 p2 = true <->
    exists p2', eval_pmap m p1 p2' = true /\
          (forall x, x <> i -> array_get p2 x = array_get p2' x).

(** Set an out dimension to be equal to the value of an aff **)
Axiom pmap_set_dim_equal_to_pwaff : forall {n m}, PMap n m -> PwAff n -> Fin m -> PMap n m.
Axiom eval_pmap_set_dim_equal_to_pwaff :
  forall n1 n2 (m: PMap n1 n2) pwaff pos p1 p2,
    eval_pmap (pmap_set_dim_equal_to_pwaff m pwaff pos) p1 p2 =
    andb (eval_pmap m p1 p2)
    (eval_pwaff pwaff p1 ==b Some (array_get p2 pos)).

Lemma id_pmap_eq :
  forall n p, eval_pmap (id_pmap n) p p = true.
Proof.
  intros.
  apply eval_id_pmap.
  reflexivity.
Qed.

Hint Rewrite
     eval_aff_const eval_aff_var eval_aff_plus eval_aff_mul
     eval_empty_pset eval_universe_pset eval_union_pset eval_intersect_pset
     eval_subtract_pset eval_pwaff_from_aff eval_pwaff_intersect_domain eval_max_pwaff
     eval_empty_pmap eval_universe_pmap eval_id_pmap eval_union_pmap eval_intersect_pmap
     eval_pmap_set_dim_equal_to_pwaff eval_intersect_domain_pmap eval_intersect_range_pmap
     eval_ne_set_pwaff eval_eq_set_pwaff
  : rwpresburger.

Program Instance ImpPresburgerAbstractDomain : forall n, AbstractDomain (State n * State n) (PMap n n) :=
  {
  bot := empty_pmap n n;
  top := universe_pmap n n;
  join := union_pmap;

  gamma m p := eval_pmap m (fst p) (snd p) = true;
  }.
Next Obligation.
  apply eval_universe_pmap.
Qed.
Next Obligation.
  unfold Ensembles.In.
  rewrite eval_empty_pmap.
  auto.
Qed.
Next Obligation.
  unfold Ensembles.In in *.
  simpl in *.
  rewrite eval_union_pmap.
  rewrite H.
  reflexivity.
Qed.
Next Obligation.
  unfold Ensembles.In in *.
  simpl in *.
  rewrite eval_union_pmap.
  rewrite H, Bool.orb_true_r.
  reflexivity.
Qed.

Program Instance ImpPresburgerRelationalAbstractDomain
  : forall n, RelationalAbstractDomain (ImpPresburgerAbstractDomain n) :=
  {
  id_relation := id_pmap n;
  compose_relation := compose_pmap;
  compose_transitive := transitive_closure_pmap;
  }.
Next Obligation.
  apply eval_id_pmap.
  reflexivity.
Qed.
Next Obligation.
  apply eval_compose_pmap.
  eauto.
Qed.
Next Obligation.
  apply eval_transitive_closure_pmap.
  remember (c1, c2).
  generalize dependent c1.
  generalize dependent c2.
  induction H; intros; inversion Heqp; subst; [ constructor | ].
  eauto using tc_app.
Qed.


Program Instance ImpPresburgerTransferFunction : forall n, TransferFunction (ImpPresburgerAbstractDomain n) :=
  {
  transfer_binop res opc op1 op2 :=
    match opc with
    | Add => pmap_set_dim_equal_to_pwaff
              (pmap_project_out_out_dim (id_pmap n) res)
              (pwaff_from_aff (aff_plus (aff_var op1) (aff_var op2))) res
    | Mul => universe_pmap n n
    | Le => universe_pmap n n
    end;

  filter_true_value :=
    fun i => intersect_domain_pmap (universe_pmap n n) (ne_set_pwaff (pwaff_from_aff (aff_var i)) (pwaff_from_aff (aff_const n 0)));

  filter_false_value :=
    fun i => intersect_domain_pmap (universe_pmap n n) (eq_set_pwaff (pwaff_from_aff (aff_var i)) (pwaff_from_aff (aff_const n 0)));

  }.
Next Obligation.
  destruct opc; autorewrite with rwpresburger rwutils; auto.
  inversion H. subst. simpl in *.
  autorewrite with rwpresburger rwutils rweq.
  apply eval_pmap_project_out_out_dim.
  exists s.
  autorewrite with rwpresburger rwutils.
  split; [ reflexivity | ].
  intros.
  autorewrite with rwutils.
  reflexivity.
Qed.

Next Obligation.
  autorewrite with rwpresburger rwutils rweq.
  reflexivity.
Qed.

Next Obligation.
  autorewrite with rwpresburger rwutils rweq.
  rewrite H.
  autorewrite with rweq.
  reflexivity.
Qed.
