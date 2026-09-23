Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope cat.

Section Coforks.
Context (D : category).

Definition cofork := ∑ (x y z : D) 
  (f : D⟦x, y⟧) (g : D⟦x, y⟧) (e : D⟦y, z⟧),
  f · e = g · e.

Definition make_cofork (x y z : D)
  (f : D⟦x, y⟧) (g : D⟦x, y⟧) (e : D⟦y, z⟧)
  (eq : f · e = g · e) 
  : cofork
  := (x ,, y ,, z ,, f ,, g ,, e ,, eq).

Context (cf : cofork).

Definition cofork_ob1 : D := pr1 cf.
Definition cofork_ob2 : D := pr12 cf.
Definition cofork_ob3 : D := pr122 cf.
Definition cofork_par_arrow1 : D⟦cofork_ob1, cofork_ob2⟧  := pr1 (pr222 cf).
Definition cofork_par_arrow2 : D⟦cofork_ob1, cofork_ob2⟧  := pr12 (pr222 cf).
Definition cofork_arrow : D⟦cofork_ob2, cofork_ob3⟧  := pr122 (pr222 cf).
Definition cofork_eq 
  : cofork_par_arrow1 · cofork_arrow = cofork_par_arrow2 · cofork_arrow
  := pr222 (pr222 cf).

Definition is_coeq_fork
  := isCoequalizer cofork_par_arrow1 cofork_par_arrow2 cofork_arrow cofork_eq.
End Coforks.

Definition map_cofork
  {C D : category} (U : D⟶ C)
  (cf : cofork D) : cofork C.
Proof.
  use make_cofork.
  - use U; use cofork_ob1; assumption.
  - use U; use cofork_ob2; assumption.
  - use U; use cofork_ob3; assumption.
  - use #U; use cofork_par_arrow1; assumption.
  - use #U; use cofork_par_arrow2; assumption.
  - use #U; use cofork_arrow; assumption.
  - abstract (do 2 rewrite <- functor_comp; use maponpaths; use cofork_eq).
Defined.

Section USplitCoequalizers.
Context {C D : category} (U : D⟶ C).

Definition U_split_coequalizer_data : UU 
  := ∑ (x y : D) (z : C),
      D⟦x, y⟧ × D⟦x, y⟧ × C⟦U y, z⟧ × C⟦z, U y⟧ × C⟦U y, U x⟧.

(* The situation is as follow
       <---t----
   U x ---Uf---> Uy ---e---> z
       ---Ug--->    <--s----
*)

Definition U_split_coequalizer_law 
  (data : U_split_coequalizer_data)
  : UU.
Proof.
  induction data as [x [y [z [f [g [e [s t]]]]]]].
  use (_ × _ × _ × _).
  - exact (#U f · e = #U g · e).
  - exact (s · e = identity _).
  - exact (e · s = t · #U g).
  - exact (t · #U f = identity _).
Defined.

Lemma isaprop_U_split_coequalizer_law
  (data : U_split_coequalizer_data)
  : isaprop (U_split_coequalizer_law data).
Proof.
  repeat use isapropdirprod; use homset_property.
Qed.

Definition U_split_coequalizer
  := ∑ (data : U_split_coequalizer_data), U_split_coequalizer_law data. 

Section USplitCoequalizersAreCoequilizers.
Context (scoeq : U_split_coequalizer).

Let x : D := pr11 scoeq.
Let y : D := pr121 scoeq.
Let z : C := pr1 (pr221 scoeq).
Let f : D⟦x, y⟧ := pr12 (pr221 scoeq).
Let g : D⟦x, y⟧ := pr122 (pr221 scoeq).
Let e : C⟦U y, z⟧ := pr1 (pr222 (pr221 scoeq)).
Let s : C⟦z, U y⟧ := pr12 (pr222 (pr221 scoeq)).
Let t : C⟦U y, U x⟧ := pr22 (pr222 (pr221 scoeq)).

Let Ufe_Uge : #U f · e = #U g · e := pr12 scoeq.
Let se_id : s · e = identity _ := pr122 scoeq.
Let es_tUg : e · s = t · #U g := pr1 (pr222 scoeq).
Let tUf_id : t · #U f = identity _ := pr2 (pr222 scoeq).

Lemma U_split_coequalizer_is_coequalizer
  : isCoequalizer (#U f) (#U g) e Ufe_Uge.
Proof.
  intros w k Ufk_Ugk.
  use unique_exists; cbn.
  - exact (s · k).
  - rewrite assoc.
    etrans.
    { apply cancel_postcomposition; use es_tUg. }
    etrans.
    { rewrite <- assoc; apply cancel_precomposition; use (!Ufk_Ugk). }
    rewrite assoc; etrans.
    { apply cancel_postcomposition; use tUf_id. }
    use id_left.
  - intro; use homset_property.
  - intros l eq; now rewrite <- eq, assoc, se_id, id_left.
Qed.
End USplitCoequalizersAreCoequilizers.

Section CreatesUSplitCoequalizers1.
Context (scoeq : U_split_coequalizer).

Let x : D := pr11 scoeq.
Let y : D := pr121 scoeq.
Let z : C := pr1 (pr221 scoeq).
Let f : D⟦x, y⟧ := pr12 (pr221 scoeq).
Let g : D⟦x, y⟧ := pr122 (pr221 scoeq).
Let e : C⟦U y, z⟧ := pr1 (pr222 (pr221 scoeq)).
Let s : C⟦z, U y⟧ := pr12 (pr222 (pr221 scoeq)).
Let t : C⟦U y, U x⟧ := pr22 (pr222 (pr221 scoeq)).

Let Ufe_Uge : #U f · e = #U g · e := pr12 scoeq.
Let se_id : s · e = identity _ := pr122 scoeq.
Let es_tUg : e · s = t · #U g := pr1 (pr222 scoeq).
Let tUf_id : t · #U f = identity _ := pr2 (pr222 scoeq).

Definition creates_U_split_coequalizers_1
  := ∑ (z' : Coequalizer f g), z_iso z (U (CoequalizerObject z')).
End CreatesUSplitCoequalizers1.

Section CreatesUSplitCoequalizers2.
  (* A cofork whose image is a split coequalizer *)
Context (
  cf_image_scoeq: ∑
      (cf : cofork D)
      (s : C⟦U (cofork_ob3 _ cf), U (cofork_ob2 _ cf)⟧)
      (t : C⟦U (cofork_ob2 _ cf), U (cofork_ob1 _ cf)⟧),
        s · #U (cofork_arrow _ cf) = identity _ 
      × t · #U (cofork_par_arrow1 _ cf) = identity _
  ).

Let cf : cofork D := pr1 cf_image_scoeq.
Let f := cofork_par_arrow1 _ cf.
Let g := cofork_par_arrow2 _ cf.
Let e := cofork_arrow _ cf.
Let fe_ge := cofork_eq _ cf.

Definition creates_U_split_coequalizers_2
  := isCoequalizer f g e fe_ge.
End CreatesUSplitCoequalizers2.

Check creates_U_split_coequalizers_2.

Definition creates_U_split_coequalizers
  := (∏ scoeq, creates_U_split_coequalizers_1 scoeq)
  × (∏ cf_image_scoeq, creates_U_split_coequalizers_2 cf_image_scoeq).
End USplitCoequalizers.

Definition monad_induced_U_split_coequalizers {C : category} (T : Monad C)
  : MonadAlg T → U_split_coequalizer (forget_Alg T).
Proof.
  intros [[A a] Aa_laws].
  use tpair; cbn.
  - use (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    { use ((_ ,, _) ,, _ ,, _).
      + exact (T (T A)).
      + use μ.
      + abstract(use Monad_law1).
      + abstract(symmetry; use Monad_law3). }
    { use ((_ ,, _) ,, _ ,, _).
      + exact (T A).
      + use μ.
      + abstract(use Monad_law1).
      + abstract(symmetry; use Monad_law3). }
    { exact A. }
    { exists (μ _ _); abstract(use pathsinv0; use Monad_law3). }
    { exists (#T a); abstract(use pathsinv0; use (nat_trans_ax (μ T))). }
    { exact a. }
    { exact (η _ _). }
    { exact (η _ _). }
  - unfold U_split_coequalizer_law; cbn.
    abstract (
      exact (
        pr2 Aa_laws ,,
        pr1 Aa_laws ,,
        nat_trans_ax (η T) _ _ a ,,
        Monad_law1 A
      )
    ).
Defined.

Section MonadicAdjunctions.
  Context {C D : category}.
  Context (L : C ⟶ D) (R : D ⟶ C).
  Context (adj : are_adjoints L R).

  (* The situation is as follow

       -----L---->
     C      ⊥      D
       <----R-----
   *)

  Local Definition T : Monad C
    := Monad_from_adjunction adj.

  (* Eilenberg-Moore category Cᵀ *)
  Local Definition CT : category
    := MonadAlg T.

  Definition comparison_functor_data : functor_data D CT.
  Proof.
    use make_functor_data.
    - intro d; use tpair; cbn.
      + exists (R d); use #R; exact (counit_from_are_adjoints adj d).
      + exists (triangle_id_right_ad _ _); cbn.
        abstract (
          do 2 rewrite <- functor_comp; apply maponpaths;
          apply (!nat_trans_ax (counit_from_are_adjoints adj) _ _ _)
        ).
    - intros d d' f; exists (#R f).
      abstract (
        unfold is_Algebra_mor; cbn;
        do 2 rewrite <- functor_comp; apply maponpaths;
        use (!nat_trans_ax (counit_from_are_adjoints adj) _ _ _)
      ).
  Defined.

  Lemma comparison_functor_is_functor
    : is_functor comparison_functor_data.
  Proof.
    split.
    - intro.
      use subtypePath.
      { intro; use homset_property. }
      use functor_id.
    - intros ? ? ? ? ?.
      use subtypePath.
      { intro; use homset_property. }
      use functor_comp.
  Qed.

  Definition comparison_functor : D ⟶  CT.
  Proof.
    use make_functor.
    - exact comparison_functor_data.
    - exact comparison_functor_is_functor.
  Defined.

  Lemma comparison_functor_to_forgetful
    : comparison_functor ∙ forget_Alg T = R.
  Proof.
    use functor_eq.
    - use homset_property.
    - reflexivity.
  Qed.

  Lemma comparison_functor_of_free
    : L ∙ comparison_functor = free_Alg T.
  Proof.
    use functor_eq; [use homset_property|].
    use functor_data_eq.
    + intro; cbn.
      use total2_paths_f; cbn.
      * reflexivity.
      * abstract (use proofirrelevance; use isapropdirprod; use homset_property).
    + intros ? ? ?.
      Opaque total2_paths_f.
      use subtypePath.
      { intro; use homset_property. }
      unfold Univalence.double_transport; simpl.
      unfold Algebra_mor; do 2 rewrite transportf_total2; cbn.
      etrans.
      { apply maponpaths; use (transportf_total2_paths_f (λ z, C⟦pr1 z , R (L C2)⟧)
          (idpath _) _ (pr1 (#(free_Alg T) f))).  }
      use (transportf_total2_paths_f (λ z, C⟦R (L C1) , pr1 z⟧)
          (idpath _) _ (pr1 (#(free_Alg T) f))).
  Qed.

  Definition is_monadic 
    := adj_equivalence_of_cats comparison_functor.

  Definition is_strict_monadic 
    := is_catiso comparison_functor.

  Lemma isaprop_is_strict_monadic
    : isaprop is_strict_monadic.
  Proof.
    use isaprop_is_catiso.
  Qed.

  (*
  Definition monadicity_theorem_1 (mnd : is_monadic)
    : creates_U_split_coequalizers R.
  Proof.
    pose (Φ := comparison_functor).
    pose (Ψ := adj_equivalence_inv mnd).
    split.
    - intros [[x [y [z [f [g [e [s t]]]]]]] [Ufe_Uge [se_id [es_tUg tUf_id]]]].
      unfold creates_U_split_coequalizers_1; cbn.
      transparent assert (z'' : (Coequalizer (#Ψ (#Φ f)) (#Ψ (#Φ g)))).
      { eapply make_Coequalizer; use left_adjoint_preserves_coequalizer.
        + use adj_from_equiv; use adj_equivalence_of_cats_inv. 
        + use ((R (L z) ,, _),, _ ,, _); cbn.
          { exact (#R (counit_from_are_adjoints adj (L z))). }
          { abstract (use triangle_id_right_ad). }
          { abstract (
              do 2 rewrite <- functor_comp; use maponpaths;
              exact (!nat_trans_ax (counit_from_are_adjoints adj) _ _ _)
            ). }
        + exists (e · unit_from_are_adjoints adj z).
          etrans; cbn.
          { apply cancel_precomposition;
            use (nat_trans_ax (unit_from_are_adjoints adj)). }
          cbn.
          rewrite assoc.
          etrans.
          { apply cancel_postcomposition.
            use triangle_id_right_ad.
          rewrite <- functor_comp.
        + cbn.
          use subtypePath.
          admit.
          cbn.
          use Ufe_Uge.
      use (make_Coequalizer _ _ _ _ _ ,, _).
      + e

  Admitted.

  Definition monadicity_theorem_2 (hyp : creates_U_split_coequalizers R)
    : is_monadic.
  Admitted.

   *)
End MonadicAdjunctions.

Proposition monadic_adjunction_trivial
  {C D : category}
  (T : Monad C)
  : is_strict_monadic (free_Alg T) (forget_Alg T) (free_forgetful_are_adjoints T).
Proof.
  split.
  - intros x y; cbn.
    use (weqproperty (weq_iso _ _ _ _)); cbn.
    + exact (λ u, u).
    + abstract (intro; use pair_path_in2; use proofirrelevance; use homset_property).
    + abstract (intro; use pair_path_in2; use proofirrelevance; use homset_property).
  - use (weqproperty (weq_iso _ _ _ _)); cbn.
    + exact (λ u, u).
    + abstract (intro; use pair_path_in2; use proofirrelevance; use isapropdirprod; use homset_property).
    + abstract (intro; use pair_path_in2; use proofirrelevance; use isapropdirprod; use homset_property).
Qed.
