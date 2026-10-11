Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.SplitMonicsAndEpis.

Local Open Scope cat.

Section SplitCoequalizers.
Context {C : category}.
Context {x y : C}.
Context {f g : C⟦x, y⟧}.

Definition split_coequalizer_data (f g : C⟦x, y⟧) : UU 
  := ∑ (z : C) (e : C⟦y,z⟧), is_split_epi f × is_split_epi e.

Definition split_coequalizer_ob
  (d : split_coequalizer_data f g) : C
  := pr1 d.

Definition split_coequalizer_arrow
  (d : split_coequalizer_data f g) : C⟦y, split_coequalizer_ob d⟧
  := pr12 d.

Definition split_coequalizer_section1 (d : split_coequalizer_data f g) 
  : is_split_epi f
  := pr122 d.

Definition split_coequalizer_section2 (d : split_coequalizer_data f g) 
  : is_split_epi (split_coequalizer_arrow d)
  := pr222 d.

Definition split_coequalizer_section1_arrow
  (d : split_coequalizer_data f g) : C⟦y, x⟧
  := pr1 (split_coequalizer_section1 d).

Definition split_coequalizer_section2_arrow
  (d : split_coequalizer_data f g) : C⟦split_coequalizer_ob d, y⟧
  := pr1 (split_coequalizer_section2 d).

Definition split_coequalizer_law
  (d : split_coequalizer_data f g) : UU
  := 
    f · split_coequalizer_arrow d = g · split_coequalizer_arrow d
  × 
    split_coequalizer_arrow d · split_coequalizer_section2_arrow d
    = split_coequalizer_section1_arrow d · g.

Lemma isaprop_split_coequalizer_law (d : split_coequalizer_data f g)
  : isaprop (split_coequalizer_law d).
Proof.
  use isapropdirprod; use homset_property.
Qed.

Definition split_coequalizer := 
  ∑ (d :split_coequalizer_data f g), split_coequalizer_law d.

Coercion split_coequalizer_to_data (d : split_coequalizer)
  := pr1 d.

Definition split_coequalizer_section1_law (d : split_coequalizer) 
  : split_coequalizer_section1_arrow d · f = identity _
  := pr2 (split_coequalizer_section1 d).

Definition split_coequalizer_section2_law (d : split_coequalizer) 
  : split_coequalizer_section2_arrow d · split_coequalizer_arrow d = identity _
  := pr2 (split_coequalizer_section2 d).

Definition split_coequalizer_zigzag_law (d : split_coequalizer) 
  : split_coequalizer_arrow d · split_coequalizer_section2_arrow d
    = split_coequalizer_section1_arrow d · g
  := pr22 d.

Definition split_coequalizer_coeq_law (d : split_coequalizer) 
  : f · split_coequalizer_arrow d
    = g · split_coequalizer_arrow d
  := pr12 d.

Definition make_split_coequalizer
  {z : C} (e : C⟦y, z⟧)
  (hyp_f : is_split_epi f)
  (hyp_e : is_split_epi e)
  (eq1 : f · e = g · e)
  (eq2 : e · pr1 hyp_e = pr1 hyp_f · g)
  : split_coequalizer.
Proof.
  exists (z,, e,, hyp_f,, hyp_e).
  exact (eq1 ,, eq2).
Defined.

Proposition split_coequalizer_isCoequalizer
  (d :split_coequalizer)
  : isCoequalizer f g (split_coequalizer_arrow d) (split_coequalizer_coeq_law d).
Proof.
  intros w h eq; use unique_exists; simpl.
  - exact (split_coequalizer_section2_arrow d · h).
  - abstract (
      now rewrite assoc, split_coequalizer_zigzag_law,
              <- assoc, <- eq, assoc,
              split_coequalizer_section1_law, id_left
    ).
  - abstract (intro; use homset_property).
  - abstract (intros k k_eq; now rewrite <- k_eq, assoc, split_coequalizer_section2_law, id_left).
Defined.

End SplitCoequalizers.

Opaque split_coequalizer_isCoequalizer.

Arguments split_coequalizer {_} {_} {_} _ _.

Definition map_split_coequalizer {C D : category} (F : C ⟶ D)
  {x y : C} (f g : C⟦x, y⟧)
  : split_coequalizer f g → split_coequalizer (#F f) (#F g).
Proof.
  intro d; use make_split_coequalizer.
  - exact (F (split_coequalizer_ob d)).
  - exact (#F (split_coequalizer_arrow d)).
  - use functor_preserves_split_epi; use (split_coequalizer_section1 d).
  - use functor_preserves_split_epi; use (split_coequalizer_section2 d).
  - abstract (do 2 rewrite <- functor_comp; apply maponpaths; use split_coequalizer_coeq_law).
  - abstract (cbn; do 2 rewrite <- functor_comp; use maponpaths; use split_coequalizer_zigzag_law).
Defined.

(*

Definition strictly_creates_coequalizers_of_U_split_pairs
  {C D : category} (U : C ⟶  D) : UU
  := ∏ {x y : C} (f g : C⟦x,y⟧) (d : split_coequalizer (#U f) (#U g)),
     ∃! {z : C} (q : C⟦y, z⟧)
        (i : U z = split_coequalizer_ob d)
        (eq : f · q = g · q),
     transportb (λ u, D⟦U y, u⟧) i (split_coequalizer_arrow d) = #U q 
     × isCoequalizer f g q eq.
 *)

Definition strictly_creates_coequalizers_of_U_split_pairs
  {C : category} (disp_D : disp_cat C)
  (D := total_category disp_D)
  (U := pr1_category disp_D)
  : UU
  := ∏ {x y : D} (f g : D⟦x,y⟧)
      (d : split_coequalizer (#U f) (#U g))
      (z := split_coequalizer_ob d)
      (e := split_coequalizer_arrow d),
     ∃! (z_structure : disp_D z)
        (e_structure : pr2 y -->[ e ] z_structure)
        (e' : D⟦y, z ,, z_structure⟧ := e ,, e_structure)
        (eq : f · e' = g · e'),
     isCoequalizer f g e' eq.

Lemma isaprop_strictly_creates_coequalizers_of_U_split_pairs
  {C : category} (disp_D : disp_cat C)
  : isaprop (strictly_creates_coequalizers_of_U_split_pairs disp_D).
Proof.
  do 5 (use impred_isaprop; intro); use isapropiscontr.
Qed.

Section ForgetfulAlgebraFunctorStrictlyCreatesCoequalizers.
  Context {C :category} (T : Monad C).

  Let U : MonadAlg_disp T ⟶ C
    := forget_Alg_disp T.

  Let Alg_map (T : Monad C) (X : MonadAlg_disp T) : C⟦T X, X⟧ := pr12 X.

  Context (X Y : MonadAlg_disp T)
    (f g : MonadAlg_disp T⟦X, Y⟧)
    (d : split_coequalizer (# U f) (# U g)).

  Let Z : C := split_coequalizer_ob d.
  Let h : C⟦Y, Z⟧ := split_coequalizer_arrow d.

  Local Definition h_Coequalizer 
    : Coequalizer (#U f) (#U g).
  Proof.
    eapply make_Coequalizer.
    now use split_coequalizer_isCoequalizer.
  Defined.

  Local Definition Th_Coequalizer 
    : Coequalizer (#T f) (#T g).
  Proof.
    eapply make_Coequalizer.
    use split_coequalizer_isCoequalizer.
    now use map_split_coequalizer.
  Defined.

  Local Lemma z_arrow_subproof
    : # T f · Alg_map T Y · h = # T g · Alg_map T Y · h.
  Proof.
    etrans.
    { apply cancel_postcomposition; symmetry; use (pr2 f). }
    etrans.
    2: { apply cancel_postcomposition; use (pr2 g). }
    do 2 rewrite <- assoc; apply cancel_precomposition.
    use split_coequalizer_coeq_law.
  Qed.

  Local Definition z_arrow : C⟦T Z, Z⟧.
  Proof.
    use (CoequalizerOut Th_Coequalizer).
    - exact (Alg_map T Y · h).
    - abstract (do 2 rewrite assoc; use z_arrow_subproof).
  Defined.

  Local Definition Z_algebra_data : Algebra_data T.
  Proof.
    eexists; use z_arrow.
  Defined.

  Local Lemma Z_algebra_laws : Algebra_laws T Z_algebra_data.
  Proof.
    split; cbn.
    - use (EpiisEpi _ (split_epi_to_epi (h ,, split_coequalizer_section2 d))); 
      cbn; rewrite assoc, id_right.
      etrans.
      { apply cancel_postcomposition; apply (nat_trans_ax (η T) _ _ h). }
      rewrite <- id_left; etrans.
      2: { apply cancel_postcomposition; use (pr122 Y). }
      do 2 rewrite <- assoc; apply cancel_precomposition.
      use (CoequalizerCommutes Th_Coequalizer).
    - transparent assert (T2h : (split_epi (T (T Y)) (T (T Z)))).
      { exists (#T (#T h)); do 2 eapply functor_preserves_split_epi; 
        use split_coequalizer_section2. }
      use (EpiisEpi _ (split_epi_to_epi T2h)); cbn; clear T2h.
      symmetry.
      do 2 rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        rewrite <- functor_comp; apply maponpaths.
        use (CoequalizerCommutes Th_Coequalizer). }
      rewrite functor_comp.
      etrans.
      { rewrite <- assoc; apply cancel_precomposition.
        use (CoequalizerCommutes Th_Coequalizer). }
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition; symmetry; use (pr222 Y). }
      etrans.
      2: { apply cancel_postcomposition; symmetry; use (nat_trans_ax (μ T)). }
      do 2 rewrite <- assoc; apply cancel_precomposition.
      symmetry; use (CoequalizerCommutes Th_Coequalizer).
  Qed.
  
  Local Definition Z_algebra : MonadAlg_disp T := Z ,, z_arrow ,, Z_algebra_laws.

  Local Definition h_algebra_mor : MonadAlg_disp T ⟦Y, Z_algebra⟧.
  Proof.
    eexists; abstract (use pathsinv0; use (CoequalizerCommutes Th_Coequalizer)).
  Defined.

  Local Lemma h_algebra_mor_is_coequalizer_subproof
    : (f : MonadAlg_disp T ⟦ X, Y ⟧) · h_algebra_mor 
      = (g : MonadAlg_disp T ⟦ X, Y ⟧) · h_algebra_mor.
  Proof.
    use subtypePath.
    { intro; use homset_property. }
    cbn.
    use split_coequalizer_coeq_law.
  Qed.

  Section FixACone.
    Context (W : MonadAlg_disp T) (k : MonadAlg_disp T ⟦ Y, W ⟧) (eq : f · k = g · k).

    Local Definition j : C⟦Z_algebra, W⟧
      := CoequalizerOut h_Coequalizer _ _ (maponpaths pr1 eq).

    Local Lemma j_is_algebra_mor
      : pr2 Z_algebra -->[j] pr2 W.
    Proof.
      transparent assert (Th : (split_epi (T Y) (T Z))).
      { exists (#T h); eapply functor_preserves_split_epi; use split_coequalizer_section2. }
      use (EpiisEpi _ (split_epi_to_epi Th)); cbn; clear Th.
      do 2 rewrite assoc.
      etrans.
      { apply cancel_postcomposition; use (CoequalizerCommutes Th_Coequalizer). }
      etrans.
      { rewrite <- assoc; apply cancel_precomposition; use (CoequalizerCommutes h_Coequalizer). }
      etrans.
      2: { rewrite <- functor_comp; apply cancel_postcomposition; apply maponpaths.
        apply pathsinv0; use (CoequalizerCommutes h_Coequalizer). }
      use (pr2 k).
    Qed.

    Local Definition j_algebra_mor : MonadAlg_disp T⟦Z_algebra, W⟧
      := j ,, j_is_algebra_mor.

    Local Lemma j_property
      : h_algebra_mor · j_algebra_mor = k.
    Proof.
      use subtypePath.
      { intro; use homset_property. }
      use (CoequalizerCommutes h_Coequalizer).
    Qed.

    Context (j' : MonadAlg_disp T⟦Z_algebra, W⟧).
    Context (j'_property : h_algebra_mor · j' = k).

    Local Lemma j_unique
      : j' = j_algebra_mor.
    Proof.
      use subtypePath.
      { intro; use homset_property. }
      use (CoequalizerOutsEq h_Coequalizer); cbn.
      exact (maponpaths pr1 j'_property @ !maponpaths pr1 j_property).
    Qed.
  End FixACone.

  Local Lemma h_algebra_mor_is_coequalizer
    : isCoequalizer (f : MonadAlg_disp T ⟦X,Y⟧) (g : MonadAlg_disp T ⟦X,Y⟧) 
      h_algebra_mor h_algebra_mor_is_coequalizer_subproof.
  Proof.
    intros W k eq.
    use unique_exists; simpl.
    - use (j_algebra_mor _ k eq).
    - abstract use j_property.
    - abstract (intro; use (homset_property (MonadAlg_disp T))).
    - abstract use j_unique.
  Defined.

  Context (Z_structure' : Algebra_disp_cat T Z).
  Context (h_structure' : pr2 Y -->[ h] Z_structure').
  
  Let Z' : MonadAlg_disp T := Z ,, Z_structure'.
  Let h' : Y --> Z' := h ,, h_structure'.

  Context (eq : f · h' = g · h').
  Context (coeq : isCoequalizer f g h' eq).

  Local Lemma Z_structure_unique
    : Z_structure' = pr2 Z_algebra.
  Proof.
    use subtypePath.
    { intro; use isapropdirprod; use homset_property. }
    use (CoequalizerOutsEq Th_Coequalizer); cbn.
    exact (!h_structure' @ !CoequalizerCommutes Th_Coequalizer _ _ _).
  Qed.
End ForgetfulAlgebraFunctorStrictlyCreatesCoequalizers.

(* Proposition 5.4.10 in Category Theory in Context *)
Proposition forgetful_algebra_functor_creates_coequalizers_of_U_split_pairs
  {C : category} (T : Monad C)
  : strictly_creates_coequalizers_of_U_split_pairs (Algebra_disp_cat T).
Proof.
  intros x y f g d.
  use make_iscontr.
  - exists (pr2 (Z_algebra _ _ _ f g d)).
    exists (pr2 (h_algebra_mor _ _ _ _ _ _)).
    abstract (
      use tpair;
      [
        use subtypePath; 
        [intro; use homset_property
        |use split_coequalizer_coeq_law]
      |
        use h_algebra_mor_is_coequalizer
      ]
    ).
  - abstract (
      intros [z [q [eq hyp]]];
      use subtypePath;
      [|now use Z_structure_unique];
      intro; use isaproptotal2;
      [intro; use isaproptotal2|];
      [intro; use isaprop_isCoequalizer| |]; 
      intros; use proofirrelevance; use homset_property
    ).
Defined.
        
Section MonadicAdjunctions.
  Context {C : category}.
  Context {disp_D : disp_cat C}.
  Let D : category := total_category disp_D.
  Let R : D ⟶  C := pr1_category disp_D.
  Opaque R.
  Context (L : C ⟶ D).
  Context (adj : are_adjoints L R).

  (* The situation is as follow

       -----L---->
     C      ⊥      D
       <----R-----
   *)

  Local Definition T : Monad C
    := Monad_from_adjunction adj.

  Definition comparison_functor_data : functor_data D (MonadAlg_disp T).
  Proof.
    use make_functor_data.
    - intro d; use (_ ,, _ ,, _); cbn.
      + exact (R d).
      + use #R; exact (counit_from_are_adjoints adj d).
      + exists (triangle_id_right_ad _ _); cbn.
        abstract (
          do 2 rewrite <- (functor_comp R); apply maponpaths;
          apply (!nat_trans_ax (counit_from_are_adjoints adj) _ _ _)
        ).
    - intros d d' f; exists (#R f).
      abstract (
        unfold is_Algebra_mor; cbn;
        do 2 rewrite <- (functor_comp R); apply maponpaths;
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

  Definition comparison_functor : D ⟶  (MonadAlg_disp T).
  Proof.
    use make_functor.
    - exact comparison_functor_data.
    - exact comparison_functor_is_functor.
  Defined.

  Lemma comparison_functor_to_forgetful
    : comparison_functor ∙ forget_Alg_disp T = R.
  Proof.
    use functor_eq.
    - use homset_property.
    - reflexivity.
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

  Section StrictMonadicity1.
    Context (hyp : is_strict_monadic).
    Context (x y : D).
    Context (f g : D ⟦ x, y ⟧).
    Context (d : split_coequalizer (# R f) (# R g)).
    Let Z := split_coequalizer_ob d.
    Let e := split_coequalizer_arrow d.

    Let K := comparison_functor.
    Let K' := inv_catiso (K ,, hyp).
    Let U := forget_Alg_disp T.

    Let f' := #K f.
    Let g' := #K g.

    Local Lemma unique_algebra_structure
      : ∃! (z_structure : Algebra_disp_cat T Z)
       (z' := Z ,, z_structure)
       (e_structure : pr2 (K y) -->[ e] z_structure) 
       (e' := (e,, e_structure) : MonadAlg_disp T⟦K y , z'⟧)
       (eq : f' · e' = g' · e'),
       isCoequalizer f' g' e' eq.
    Proof.
      use (forgetful_algebra_functor_creates_coequalizers_of_U_split_pairs T _ _ f' g').
    Qed.

    Let KZ : MonadAlg_disp T := Z ,, pr1 (iscontrpr1 unique_algebra_structure).
    Let Ke : MonadAlg_disp T⟦K y, KZ⟧ := e ,, pr12 (iscontrpr1 unique_algebra_structure).

    Local Lemma K'K : K'∙K = functor_identity _.
    Proof.
    Admitted.
      (*
      use funextsec; intro u; use (homotweqinvweq (catiso_ob_weq (K,, hyp)) u).
    Qed.
       *)

    (*
    Local Lemma K'KZ_pr1 : R (K' KZ) = Z.
    Proof.
      exact (maponpaths (λ f : MonadAlg_disp T ⟶ MonadAlg_disp T, U (f KZ)) K'K).
    Qed.

    Local Definition z_structure : disp_D Z
      := transportf _ K'KZ_pr1 (pr2 _).

    Local Definition e_structure : pr2 y -->[ split_coequalizer_arrow d ] z_structure.
    Proof.
      eassert _ by exact (pr2 (#K' Ke)).
      refine (transportf (λ f : MonadAlg_disp T ⟶ MonadAlg_disp T,
        pr2 (f (K y)) -->[ pr1 (#f (#K' e))] pr2 (f KZ)) K'K X).




    Goal ∃! (z_structure : disp_D Z)
      (z' := Z,, z_structure)
(e_structure : pr2 y -->[ split_coequalizer_arrow d] z_structure)
(e' : D⟦y, z'⟧ := (split_coequalizer_arrow d,, e_structure))
(eq : f · e' =
      g · e'),
isCoequalizer f g e' eq.

     *)
  End StrictMonadicity1.

  Theorem strict_monadicity_theorem_1 
    : is_strict_monadic → strictly_creates_coequalizers_of_U_split_pairs disp_D.
  Proof.
    (*
    intros hyp.
    unfold strictly_creates_coequalizers_of_U_split_pairs; fold D.
    intros x y f g d.
    pose ().
    pose ().
    transparent assert (d' : (split_coequalizer (# U (# K f)) (# U (# K g)))).
    { unfold split_coequalizer.

    show_id_type.
       *)
  Admitted.

End MonadicAdjunctions.

(*
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
   Qed. *)
