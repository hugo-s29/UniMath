Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.SubstitutionSystems.CategoryOfSignaturesWithStrength.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.ConstructionOfGHSS.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section FreeModelAdjunction.
  Context {V : category} (Mon_V : monoidal V).

  Let V_Mon : monoidal_cat := _ ,, Mon_V.

  Let PtdV : category := GeneralizedSubstitutionSystems.PtdV Mon_V.
  Let Mon_PtdV : monoidal PtdV := GeneralizedSubstitutionSystems.Mon_PtdV Mon_V.
  Let Act : actegory Mon_PtdV V:= GeneralizedSubstitutionSystems.Act Mon_V.

  Context (H : V ⟶ V) (θ : pointedtensorialstrength Mon_V H).

  (* Assumptions on V *)
  Context (CP : BinCoproducts V)
    (δ : actegory_bincoprod_distributor Mon_PtdV CP Act)
    (IV : Initial V)
    (CV : Colims_of_shape nat_graph V)
    (initial_annihilates : ∏ (v : V), isInitial V (v ⊗_{Mon_V} (InitialObject IV)))
    (left_whiskering_omega_cocont : ∏ (v : V), is_omega_cocont (leftwhiskering_functor Mon_V v))
    (right_whiskering_omega_cocont : ∏ (v : V), is_omega_cocont (rightwhiskering_functor Mon_V v)).

  (* Assumptions on H *)
  Context (HH : is_omega_cocont H).

  Local Definition forgetful : SigmaMonoid θ ⟶ V := pr1_category _.

  Section FixAnObject.
    Context (v : V).

    Definition sum_H_tens_v : V ⟶ V
      := BinCoproduct_of_functors _ _ CP H (rightwhiskering_functor Mon_V v).

    Lemma sum_H_tens_v_is_omega_cocont : is_omega_cocont sum_H_tens_v.
    Proof.
      apply is_omega_cocont_BinCoproduct_of_functors.
      - exact HH.
      - exact (right_whiskering_omega_cocont v).
    Qed.

    Definition sum_H_tens_v_strength_data
      : lineator_data Mon_PtdV Act Act sum_H_tens_v
      := λ x y, δ _ _ _ · BinCoproductOfArrows _ _ _ (θ x y) αinv^{Mon_V}_{pr1 x,y,v}.

    Lemma sum_H_tens_v_strength_laws_left
      : lineator_nat_left Mon_PtdV Act Act sum_H_tens_v sum_H_tens_v_strength_data.
    Proof.
      intros x y z f.
      cbn; unfold BinCoproduct_of_functors_mor, sum_H_tens_v_strength_data; cbn.
      repeat rewrite <- assoc.
      use (iso_inv_to_left _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ _ _ _)))).
      cbn; unfold precomp_with.
      rewrite id_right; do 2 rewrite assoc.
      use BinCoproductArrowsEq; do 4 rewrite assoc.
      + etrans.
        { do 3 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        cbn.
        rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { do 2 apply cancel_postcomposition; apply maponpaths; use BinCoproductIn1Commutes. }
        rewrite (bifunctor_leftcomp Mon_V).
        symmetry; etrans.
        { apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn1Commutes. }
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition; symmetry; use (lineator_linnatleft _ _ _ _ θ). }
        cbn.
        repeat rewrite assoc'; use cancel_precomposition; repeat rewrite assoc.
        symmetry; etrans.
        {
          use cancel_postcomposition.
          use BinCoproductIn1.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn1Commutes.
        }
        use BinCoproductIn1Commutes.
      + etrans.
        { do 3 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        cbn.
        rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { do 2 apply cancel_postcomposition; apply maponpaths; use BinCoproductIn2Commutes. }
        rewrite (bifunctor_leftcomp Mon_V).
        symmetry; etrans.
        { apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn2Commutes. }
        rewrite assoc.
        rewrite <- (monoidal_associatorinvnatleftright Mon_V).
        repeat rewrite assoc'; use cancel_precomposition; repeat rewrite assoc.
        symmetry; etrans.
        {
          use cancel_postcomposition.
          use BinCoproductIn2.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn2Commutes.
        }
        use BinCoproductIn2Commutes.
     Qed.

    Lemma sum_H_tens_v_strength_laws_right
      : lineator_nat_right Mon_PtdV Act Act sum_H_tens_v sum_H_tens_v_strength_data.
    Proof.
      intros x y z f; cbn.
      unfold BinCoproduct_of_functors_ob, sum_H_tens_v_strength_data; cbn.
      rewrite <- assoc.
      use (iso_inv_to_left _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ _ _ _)))).
      cbn; unfold precomp_with; cbn.
      rewrite id_right, assoc, assoc.
      use BinCoproductArrowsEq; do 4 rewrite assoc; symmetry.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn1Commutes. }
        simpl; rewrite assoc; etrans.
        { apply cancel_postcomposition. symmetry; use (lineator_linnatright _ _ _ _ θ). }
        cbn; symmetry; etrans.
        { do 3 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        cbn; etrans.
        { do 2 apply cancel_postcomposition; symmetry; use (bifunctor_equalwhiskers Mon_V). }
        etrans; unfold functoronmorphisms1.
        {
          use cancel_postcomposition.
          exact (pr1 f ⊗^{Mon_V}_{r} _ · BinCoproductIn1 _).
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          rewrite assoc'; use cancel_precomposition.
          symmetry; use BinCoproductIn1Commutes.
        }
        do 2 rewrite assoc'; use cancel_precomposition.
        use BinCoproductOfArrowsIn1.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn2Commutes. }
        simpl; rewrite assoc, <- (monoidal_associatorinvnatright Mon_V).
        cbn; symmetry; etrans.
        { do 3 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        cbn; etrans.
        { do 2 apply cancel_postcomposition; symmetry; use (bifunctor_equalwhiskers Mon_V). }
        etrans; unfold functoronmorphisms1.
        {
          use cancel_postcomposition.
          exact (pr1 f ⊗^{Mon_V}_{r} _ · BinCoproductIn2 _).
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          rewrite assoc'; use cancel_precomposition.
          symmetry; use BinCoproductIn2Commutes.
        }
        do 2 rewrite assoc'; use cancel_precomposition.
        use BinCoproductOfArrowsIn2.
    Qed.

    Lemma sum_H_tens_v_strength_laws_unitor
      : preserves_unitor Mon_PtdV Act Act sum_H_tens_v sum_H_tens_v_strength_data.
    Proof.
      intro x; cbn.
      unfold reindexed_action_unitor_data, sum_H_tens_v_strength_data; cbn.
      do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      rewrite <- assoc; symmetry.
      use (iso_inv_to_left _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ (_ ,, identity _) _ _)))).
      cbn; unfold precomp_with; cbn; rewrite id_right.
      use BinCoproductArrowsEq; do 2 rewrite assoc; symmetry.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        etrans.
        2: { apply cancel_postcomposition; symmetry; use BinCoproductIn1Commutes. }
        cbn; rewrite (monoidal_leftunitornat Mon_V).
        etrans.
        { rewrite <- assoc; apply cancel_precomposition; use BinCoproductOfArrowsIn1. }
        cbn; rewrite assoc; use cancel_postcomposition.
        refine (!_ @ lineator_preservesunitor _ _ _ _ θ _ @ _).
        + use cancel_precomposition; use maponpaths.
          cbn; unfold reindexed_action_unitor_data; cbn.
          now rewrite (bifunctor_rightid Mon_V), id_left.
        + cbn; unfold reindexed_action_unitor_data; cbn.
          now rewrite (bifunctor_rightid Mon_V), id_left.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        etrans.
        2: { apply cancel_postcomposition; symmetry; use BinCoproductIn2Commutes. }
        cbn; rewrite (monoidal_leftunitornat Mon_V).
        etrans.
        { rewrite <- assoc; apply cancel_precomposition; use BinCoproductOfArrowsIn2. }
        cbn; rewrite assoc; use cancel_postcomposition.
        rewrite <- (right_whisker_with_lunitor Mon_V), assoc, <- id_left.
        use cancel_postcomposition.
        use (pr2 (monoidal_associatorisolaw _ _ _ _)).
    Qed.

    Lemma sum_H_tens_v_strength_laws_actor
      : preserves_actor Mon_PtdV Act Act sum_H_tens_v sum_H_tens_v_strength_data.
    Proof.
      intros x y z; cbn.
      unfold reindexed_actor_data, sum_H_tens_v_strength_data, BinCoproduct_of_functors_mor, BinCoproduct_of_functors_ob; cbn.
      do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      repeat rewrite <- assoc; symmetry.
      use (iso_inv_to_left _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ (x ⊗_{Mon_PtdV} y) _ _)))).
      cbn; unfold precomp_with; rewrite id_right.
      use BinCoproductArrowsEq; do 5 rewrite assoc; symmetry.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        etrans. 
        { rewrite <- assoc; apply cancel_precomposition; use BinCoproductOfArrowsIn1. }
        rewrite assoc; symmetry; etrans.
        { do 4 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        cbn; rewrite <- (monoidal_associatornatleft Mon_V), (bifunctor_leftcomp Mon_V), assoc.
        etrans.
        { do 3 apply cancel_postcomposition.
          rewrite <- assoc, <- (bifunctor_leftcomp Mon_V).
          apply cancel_precomposition.
          use maponpaths.
          use BinCoproductIn1.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn1Commutes. }
        etrans.
        { do 2 apply cancel_postcomposition.
          rewrite <- assoc, <- (bifunctor_leftcomp Mon_V).
          do 2 apply maponpaths.
          use BinCoproductOfArrowsIn1. }
        rewrite bifunctor_leftcomp, assoc.
        etrans.
        { apply cancel_postcomposition; rewrite <- assoc.
          use cancel_precomposition.
          use BinCoproductIn1.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn1Commutes. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductOfArrowsIn1. }
        rewrite assoc; apply cancel_postcomposition.
        refine (_ @ !lineator_preservesactor _ _ _ _ θ x y z @ _);
        unfold actegory_actordata; cbn; unfold reindexed_actor_data; cbn;
        now rewrite (bifunctor_rightid Mon_V), id_left.
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        etrans. 
        { rewrite <- assoc; apply cancel_precomposition; use BinCoproductOfArrowsIn2. }
        rewrite assoc; symmetry; etrans.
        { do 4 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        cbn; rewrite <- (monoidal_associatornatleft Mon_V), (bifunctor_leftcomp Mon_V), assoc.
        etrans.
        { do 3 apply cancel_postcomposition.
          rewrite <- assoc, <- (bifunctor_leftcomp Mon_V).
          apply cancel_precomposition.
          use maponpaths.
          use BinCoproductIn2.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn2Commutes. }
        etrans.
        { do 2 apply cancel_postcomposition.
          rewrite <- assoc, <- (bifunctor_leftcomp Mon_V).
          do 2 apply maponpaths.
          use BinCoproductOfArrowsIn2. }
        rewrite bifunctor_leftcomp, assoc.
        etrans.
        { apply cancel_postcomposition; rewrite <- assoc.
          use cancel_precomposition.
          use BinCoproductIn2.
          rewrite <- id_right.
          etrans; [|apply cancel_precomposition; use (pr2 (pr2 δ _ _ _))].
          rewrite assoc; use cancel_postcomposition.
          symmetry; use BinCoproductIn2Commutes. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductOfArrowsIn2. }
        rewrite assoc; apply cancel_postcomposition.
        (* Pentagon axiom *)
        symmetry.
        rewrite <- id_right, <- (bifunctor_rightid Mon_V), <- (pr2 (monoidal_associatorisolaw _ _ _ _)), bifunctor_rightcomp, assoc.
        symmetry; etrans.
        { apply cancel_postcomposition; do 2 rewrite assoc';
          apply cancel_precomposition; rewrite assoc.
          use monoidal_pentagon_identity_inv. }
        rewrite assoc; use cancel_postcomposition.
        rewrite <- id_left; use cancel_postcomposition.
        use (pr1 (monoidal_associatorisolaw _ _ _ _)).
    Qed.

    Lemma sum_H_tens_v_strength_laws
      : lineator_laxlaws Mon_PtdV Act Act sum_H_tens_v sum_H_tens_v_strength_data.
    Proof.
      repeat split.
      - exact sum_H_tens_v_strength_laws_left.
      - exact sum_H_tens_v_strength_laws_right.
      - exact sum_H_tens_v_strength_laws_actor.
      - exact sum_H_tens_v_strength_laws_unitor.
    Qed.

    Definition sum_H_tens_v_strength
      : pointedtensorialstrength Mon_V sum_H_tens_v
      := sum_H_tens_v_strength_data ,, sum_H_tens_v_strength_laws.

    Definition free_sigma_monoid_ob_initial_monoid_tens_v
      : Initial (SigmaMonoid sum_H_tens_v_strength)
      := SigmaMonoidFromInitialAlgebraInitial _ _ δ _ CV sum_H_tens_v_is_omega_cocont 
          initial_annihilates left_whiskering_omega_cocont.

    Definition free_sigma_monoid_ob_monoid_tens_v
      : SigmaMonoid sum_H_tens_v_strength
      := pr1 free_sigma_monoid_ob_initial_monoid_tens_v.

    Local Definition M : V := SigmaMonoid_carrier _ free_sigma_monoid_ob_monoid_tens_v.
    Local Definition τ : V ⟦ CP (H M) (M ⊗_{ Mon_V} v), M ⟧ := SigmaMonoid_τ _ free_sigma_monoid_ob_monoid_tens_v.
    Local Definition μ : V ⟦ M ⊗_{Mon_V} M, M ⟧ := SigmaMonoid_μ _ free_sigma_monoid_ob_monoid_tens_v.
    Local Definition η : V ⟦ I_{Mon_V}, M ⟧ := SigmaMonoid_η _ free_sigma_monoid_ob_monoid_tens_v.

    Opaque free_sigma_monoid_ob_initial_monoid_tens_v.
    Opaque free_sigma_monoid_ob_monoid_tens_v.

    Definition free_sigma_monoid_ob_monoid : monoid Mon_V M
      := pr2 (SigmaMonoid_to_monoid _ free_sigma_monoid_ob_monoid_tens_v).

    Local Definition τ' : V ⟦ H M , M ⟧ := BinCoproductIn1 _ · τ.
    Local Definition p : V ⟦ M ⊗_{Mon_V} v, M ⟧ := BinCoproductIn2 _ · τ.

    Lemma free_sigma_monoid_ob_compatibility
      : SigmaMonoid_characteristic_equation M η μ τ' (θ (M ,, η) M).
    Proof.
      unfold SigmaMonoid_characteristic_equation.
      transitivity (
        BinCoproductIn1 (CP _ _)
        · BinCoproductOfArrows V _ (CP _ _)
            (θ (M,, η) M) αinv^{ Mon_V }_{ M, M, v}
        · BinCoproductOfArrows V _ _ 
          (# H μ) (μ ⊗^{ Mon_V}_{r} v)
        · τ
      ); simpl.
      2: transitivity (
          BinCoproductIn1 (CP _ _)
          · bincoprod_antidistributor _ _ (leftwhiskering_functor Mon_V M) _ _
          · M ⊗^{Mon_V}_{l} τ 
          · μ 
        ); simpl.
      - symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        do 3 rewrite <- assoc.
        use cancel_precomposition.
        rewrite assoc; etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        use assoc'.
      - repeat rewrite <- assoc.
        use cancel_precomposition.
        symmetry.
        etrans; [apply cancel_postcomposition; use (!id_right _)|].
        use (iso_inv_on_right _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ (M ,, η) _ _)))).
        simpl; do 2 rewrite assoc.
        use (!pr22 free_sigma_monoid_ob_monoid_tens_v).
      - use cancel_postcomposition.
        etrans.
        { apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        symmetry; use (bifunctor_leftcomp Mon_V).
    Qed.

    Lemma free_sigma_monoid_ob_compatibility_p
      : αinv^{ Mon_V }_{ M , M , v} · μ ⊗^{ Mon_V}_{r} v · p
      = M ⊗^{ Mon_V}_{l} p · μ.
    Proof.
      transitivity (
        BinCoproductIn2 (CP _ _)
        · BinCoproductOfArrows V _ (CP _ _)
            (θ (M,, η) M) αinv^{ Mon_V }_{ M, M, v}
        · BinCoproductOfArrows V _ _ 
          (# H μ) (μ ⊗^{ Mon_V}_{r} v)
        · τ
      ); simpl.
      2: transitivity (
          BinCoproductIn2 (CP _ _)
          · bincoprod_antidistributor _ _ (leftwhiskering_functor Mon_V M) _ _
          · M ⊗^{Mon_V}_{l} τ 
          · μ 
        ); simpl.
      - symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        do 3 rewrite <- assoc.
        use cancel_precomposition.
        rewrite assoc; etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        use assoc'.
      - repeat rewrite <- assoc.
        use cancel_precomposition.
        symmetry.
        etrans; [apply cancel_postcomposition; use (!id_right _)|].
        use (iso_inv_on_right _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ (M ,, η) _ _)))).
        simpl; do 2 rewrite assoc.
        use (!pr22 free_sigma_monoid_ob_monoid_tens_v).
      - use cancel_postcomposition.
        etrans.
        { apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        symmetry; use (bifunctor_leftcomp Mon_V).
    Qed.

    Definition free_sigma_monoid_ob : SigmaMonoid θ
      := M ,, (τ' ,, free_sigma_monoid_ob_monoid) ,, free_sigma_monoid_ob_compatibility.
  End FixAnObject.

  Opaque free_sigma_monoid_ob_initial_monoid_tens_v.

  Section FixAMorphism.
    Context (v v' : V) (f : v --> v').

    Lemma free_sigma_monoid_mor_target_sigma_monoid_compatibility
      : δ (M v',, η v') _ _ 
      · BinCoproductOfArrows V _ (CP _ _) (θ (M v',, η v') _) αinv^{ Mon_V }_{ M v', M v', v}
      · BinCoproductOfArrows V _ _ (# H (μ v')) (μ v' ⊗^{ Mon_V}_{r} v)
      · BinCoproductArrow (CP (H (M v')) (M v' ⊗_{ Mon_V} v)) (τ' v') (M v' ⊗^{ Mon_V}_{l} f · p v') 
      = M v' ⊗^{ Mon_V}_{l} BinCoproductArrow _ (τ' v') (M v' ⊗^{ Mon_V}_{l} f · p v') 
        · μ v'.
    Proof.
      simpl.
      rewrite <- id_left.
      etrans; swap 1 2.
      { apply cancel_postcomposition; use (pr1 (pr2 δ (M v' ,, η v') _ _)). }
      repeat rewrite <- assoc.
      use cancel_precomposition.
      repeat rewrite assoc.
      use BinCoproductArrowsEq; do 4 rewrite assoc.
      - symmetry.
        etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        cbn; rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths; use BinCoproductIn1Commutes. }
        symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        do 2 rewrite <- assoc; etrans.
        { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        do 2 rewrite assoc; rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn1Commutes. }
        use free_sigma_monoid_ob_compatibility.
      - symmetry.
        etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        cbn; rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths; use BinCoproductIn2Commutes. }
        symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        do 2 rewrite <- assoc; etrans.
        { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        do 2 rewrite assoc; rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn2Commutes. }
        repeat rewrite <- assoc.
        apply (z_iso_inv_on_right  _ _ _ (make_z_iso _ _ (monoidal_associatorisolaw _ _ _ _))).
        simpl; rewrite (bifunctor_leftcomp Mon_V); repeat rewrite assoc.
        rewrite (monoidal_associatornatleft Mon_V).
        etrans.
        { apply cancel_postcomposition; use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2.
        repeat rewrite <- assoc; use cancel_precomposition.
        etrans; swap 1 2.
        { apply cancel_precomposition; use free_sigma_monoid_ob_compatibility_p. }
        do 2 rewrite assoc.
        now rewrite (pr1 (monoidal_associatorisolaw Mon_V _ _ _)), id_left.
    Qed.

    Definition free_sigma_monoid_mor_target_sigma_monoid
      : SigmaMonoid (sum_H_tens_v_strength v).
    Proof.
      use (M v' ,, (_ ,, _) ,, _); cbn.
      - use BinCoproductArrow; cbn.
        + exact (τ' v').
        + exact (M v' ⊗^{Mon_V}_{l} f · p v').
      - use free_sigma_monoid_ob_monoid.
      - exact free_sigma_monoid_mor_target_sigma_monoid_compatibility.
    Defined.

    Definition free_sigma_monoid_mor_init_arrow
      : SigmaMonoid (sum_H_tens_v_strength v) 
        ⟦ free_sigma_monoid_ob_initial_monoid_tens_v v,
         free_sigma_monoid_mor_target_sigma_monoid ⟧
      := InitialArrow (free_sigma_monoid_ob_initial_monoid_tens_v v) 
        free_sigma_monoid_mor_target_sigma_monoid.

    Local Definition f_model : M v --> M v' := pr1 free_sigma_monoid_mor_init_arrow.

    Lemma free_sigma_monoid_mor_τ 
      : τ' v · f_model = # H f_model · τ' v'.
    Proof.
      unfold τ'; rewrite assoc.
      transitivity (
        BinCoproductIn1 (CP _ _) 
        · BinCoproductOfArrows V _ _ (# H f_model) (f_model ⊗^{ Mon_V}_{r} v)
        · BinCoproductArrow (CP _ _) (τ' v') (M v' ⊗^{ Mon_V}_{l} f · p v')
      ).
      - symmetry; do 2 rewrite <- assoc.
        use cancel_precomposition.
        use (!pr112 free_sigma_monoid_mor_init_arrow).
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn1Commutes. }
        use assoc.
    Qed.

    Lemma free_sigma_monoid_mor_p 
      : p v · f_model = M v ⊗^{Mon_V}_{l} f · f_model ⊗^{ Mon_V}_{r} v' · p v'.
    Proof.
      unfold p; rewrite assoc.
      transitivity (
        BinCoproductIn2 (CP _ _) 
        · BinCoproductOfArrows V _ _ (# H f_model) (f_model ⊗^{ Mon_V}_{r} v)
        · BinCoproductArrow (CP _ _) (τ' v') (M v' ⊗^{ Mon_V}_{l} f · p v')
      ).
      - symmetry; do 2 rewrite <- assoc.
        use cancel_precomposition.
        use (!pr112 free_sigma_monoid_mor_init_arrow).
      - etrans.
        { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
        rewrite <- assoc; etrans.
        { apply cancel_precomposition; use BinCoproductIn2Commutes. }
        unfold p; do 2 rewrite assoc.
        do 2 apply cancel_postcomposition.
        use (bifunctor_equalwhiskers Mon_V).
     Qed.

    Definition free_sigma_monoid_mor
      : free_sigma_monoid_ob v --> free_sigma_monoid_ob v'.
    Proof.
      use (f_model ,, (_ ,, _) ,, tt); cbn.
      - exact free_sigma_monoid_mor_τ.
      - exact (pr212 free_sigma_monoid_mor_init_arrow).
    Defined.
  End FixAMorphism.

  Definition free_sigma_monoid_data
    : functor_data V (SigmaMonoid θ).
  Proof.
    use tpair.
    - exact free_sigma_monoid_ob.
    - exact free_sigma_monoid_mor.
  Defined.

  Definition free_sigma_monoid_laws
    : is_functor free_sigma_monoid_data.
  Proof.
    split.
    - intro v.
      use invmap; [|use path_sigma_hprop|].
      { do 2 try use isapropdirprod; simpl.
        + use homset_property.
        + use isaprop_is_monoid_mor.
        + use isapropunit. }
      simpl.
      symmetry.
      transparent assert (f : (free_sigma_monoid_ob_initial_monoid_tens_v v --> free_sigma_monoid_mor_target_sigma_monoid v v (identity v))).
      { 
        use (identity _,, (_ ,, _) ,, tt); cbn.
        + abstract (
            unfold BinCoproduct_of_functors_mor; cbn;
            rewrite id_right, functor_id, (bifunctor_rightid Mon_V), 
              (bifunctor_leftid Mon_V), id_left,
              BinCoproduct_of_identities, id_left;
            use BinCoproductArrowEta
          ).
        + use id_is_monoid_mor.
      }
      use (maponpaths pr1 (InitialArrowUnique _ _ f)).
    - intros v v' v'' f f'.
      use invmap; [|use path_sigma_hprop|].
      { do 2 try use isapropdirprod; simpl.
        + use homset_property.
        + use isaprop_is_monoid_mor.
        + use isapropunit. }
      simpl.
      symmetry.
      assert (comp_lemma :
        τ v · (f_model v v' f · f_model v' v'' f') 
        = BinCoproductOfArrows V _ _ (# H (f_model v v' f · f_model v' v'' f'))
          ((f_model v v' f · f_model v' v'' f') ⊗^{ Mon_V}_{r} v)
        · BinCoproductArrow (CP _ _) (τ' v'') (M v'' ⊗^{ Mon_V}_{l} (f · f') · p v'')
      ). {
        unfold BinCoproduct_of_functors_mor; cbn.
        rewrite assoc, (bifunctor_leftcomp Mon_V), (bifunctor_rightcomp Mon_V), functor_comp.
        use BinCoproductArrowsEq; do 3 rewrite assoc; symmetry.
        + etrans.
          { apply cancel_postcomposition; apply BinCoproductOfArrowsIn1. }
          rewrite <- assoc; etrans.
          { apply cancel_precomposition; apply BinCoproductIn1Commutes. }
          now rewrite <- assoc, <- free_sigma_monoid_mor_τ, assoc, <- free_sigma_monoid_mor_τ.
        + etrans.
          { apply cancel_postcomposition; apply BinCoproductOfArrowsIn2. }
          rewrite <- assoc; etrans.
          { apply cancel_precomposition; apply BinCoproductIn2Commutes. }
          do 2 rewrite assoc.
          symmetry.
          fold (p v). 
          rewrite free_sigma_monoid_mor_p, <- assoc.
          rewrite free_sigma_monoid_mor_p, assoc, assoc.
          use cancel_postcomposition.
          do 4 rewrite (@tensor_mor_left V_Mon), (@tensor_mor_right V_Mon).
          etrans.
          { do 2 apply cancel_postcomposition; use (@tensor_swap' V_Mon). }
          rewrite <- assoc; etrans.
          { apply cancel_precomposition; use (@tensor_swap' V_Mon). }
          rewrite assoc; use cancel_postcomposition.
          do 2 rewrite <- assoc; use cancel_precomposition.
          use tensor_swap'.
      }
      transparent assert (f : (free_sigma_monoid_ob_initial_monoid_tens_v v --> free_sigma_monoid_mor_target_sigma_monoid v v'' (f · f'))).
      { 
        use (_,, (_ ,, _) ,, tt); cbn.
        + exact (f_model _ _ f · f_model _ _ f').
        + use comp_lemma.
        + eapply comp_is_monoid_mor; use (pr212 (free_sigma_monoid_mor_init_arrow _ _ _)).
      }
      use (maponpaths pr1 (InitialArrowUnique _ _ f)).
  Qed.

  Definition free_sigma_monoid : V ⟶  SigmaMonoid θ
    := make_functor free_sigma_monoid_data free_sigma_monoid_laws.

  Section HomSetMap.
    Context (X : V) (N : SigmaMonoid θ).

    Let UN : V := forgetful N.

    Definition free_sigma_monoid_adjuction_homset_map
      (g' : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧)
      : V ⟦ X, forgetful N ⟧
      := luinv^{Mon_V}_{X} · η X ⊗^{Mon_V}_{r} X · p X · pr1 g'.

    Section FixAMorphism.
      Context (f : V ⟦ X, forgetful N ⟧).

      Lemma free_sigma_monoid_adjuction_model_compatibility
        : SigmaMonoid_compatibility (sum_H_tens_v_strength X) 
          (UN,, BinCoproductArrow _ (SigmaMonoid_τ θ N) (UN ⊗^{ Mon_V}_{l} f · SigmaMonoid_μ θ N),, pr212 N).
      Proof.
      unfold SigmaMonoid_compatibility, SigmaMonoid_characteristic_equation; cbn.
      unfold sum_H_tens_v_strength_data, BinCoproduct_of_functors_mor; cbn.
      repeat rewrite <- assoc; symmetry.
      use (iso_inv_to_left _ _ _ (z_iso_to_iso (make_z_iso _ _ (pr2 δ (_ ,, SigmaMonoid_η _ N) _ _)))).
      cbn; unfold precomp_with.
      rewrite id_right; do 2 rewrite assoc.
      use BinCoproductArrowsEq; do 4 rewrite assoc.
      - etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        cbn; fold UN; rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths; use BinCoproductIn1Commutes. }
        symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn1Commutes. }
        do 2 rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition.
          apply BinCoproductOfArrowsIn1. }
        do 2 rewrite assoc; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use BinCoproductIn1Commutes. }
        use SigmaMonoid_is_compatible.
      - etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        cbn; fold UN; rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths; use BinCoproductIn2Commutes. }
        symmetry; etrans.
        { do 2 apply cancel_postcomposition; use BinCoproductIn2Commutes. }
        do 2 rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition.
          apply BinCoproductOfArrowsIn2. }
        do 2 rewrite assoc; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use BinCoproductIn2Commutes. }
        rewrite <- assoc.
        apply (z_iso_inv_on_right  _ _ _ (make_z_iso _ _ (monoidal_associatorisolaw _ _ _ _))).
        cbn; rewrite (bifunctor_leftcomp Mon_V); do 3 rewrite assoc.
        etrans.
        { apply cancel_postcomposition; use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2.
        rewrite monoidal_associatornatleft.
        do 3 rewrite <- assoc; use cancel_precomposition.
        rewrite assoc.
        use (!monoid_to_assoc_law _ (pr2 (SigmaMonoid_to_monoid _ N))).
      Qed.

      Definition free_sigma_monoid_adjuction_model
        : SigmaMonoid (sum_H_tens_v_strength X).
      Proof.
        use (UN ,, (_ ,, _) ,, _); cbn.
        - use BinCoproductArrow; cbn.
          + exact (SigmaMonoid_τ _ N).
          + exact (UN ⊗^{Mon_V}_{l} f · SigmaMonoid_μ _ N).
        - use (pr2 (SigmaMonoid_to_monoid _ N)).
        - use free_sigma_monoid_adjuction_model_compatibility.
      Defined.

      Definition free_sigma_monoid_adjuction_model_arrow
        : free_sigma_monoid_ob_initial_monoid_tens_v X --> free_sigma_monoid_adjuction_model
        := InitialArrow (free_sigma_monoid_ob_initial_monoid_tens_v X) free_sigma_monoid_adjuction_model.

      Let g : M X --> UN := pr1 free_sigma_monoid_adjuction_model_arrow.

      Definition free_sigma_monoid_adjuction_homset_invmap_τ
        : τ' X · g = # H g · SigmaMonoid_τ _ N.
      Proof.
        unfold τ'; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use (pr112 free_sigma_monoid_adjuction_model_arrow). }
        rewrite assoc; cbn; etrans.
        { apply cancel_postcomposition. use BinCoproductOfArrowsIn1. }
        cbn; fold g.
        rewrite <- assoc; use cancel_precomposition.
        use BinCoproductIn1Commutes.
      Qed.

      Definition free_sigma_monoid_adjuction_homset_invmap_p
        : p X · g = g ⊗^{Mon_V} f · SigmaMonoid_μ _ N.
      Proof.
        unfold p; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use (pr112 free_sigma_monoid_adjuction_model_arrow). }
        rewrite assoc; cbn; etrans.
        { apply cancel_postcomposition. use BinCoproductOfArrowsIn2. }
        cbn; fold g.
        unfold functoronmorphisms1.
        do 2 rewrite <- assoc; use cancel_precomposition.
        use BinCoproductIn2Commutes.
      Qed.

      Definition free_sigma_monoid_adjuction_homset_invmap
        : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧.
      Proof.
        refine (g ,, (_ ,, _) ,, tt); cbn.
        - use free_sigma_monoid_adjuction_homset_invmap_τ.
        - use (pr212 free_sigma_monoid_adjuction_model_arrow).
      Defined.

      Let f' : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧
        := free_sigma_monoid_adjuction_homset_invmap.

      Lemma free_sigma_monoid_adjuction_homset_map_invmap
        : free_sigma_monoid_adjuction_homset_map free_sigma_monoid_adjuction_homset_invmap = f.
      Proof.
        unfold free_sigma_monoid_adjuction_homset_map.
        unfold free_sigma_monoid_adjuction_homset_invmap.
        do 2 rewrite <- assoc.
        apply (z_iso_inv_on_right  _ _ _ (make_z_iso _ _ (monoidal_leftunitorisolaw _ _))); cbn.
        etrans.
        { apply cancel_precomposition; use free_sigma_monoid_adjuction_homset_invmap_p. }
        unfold functoronmorphisms1.
        rewrite assoc, <- monoidal_leftunitornat, assoc, <- (bifunctor_rightcomp Mon_V).
        etrans.
        { do 2 apply cancel_postcomposition; use maponpaths.
          + use SigmaMonoid_η.
          + use (pr2 (pr212 free_sigma_monoid_adjuction_model_arrow)). }
        etrans.
        { apply cancel_postcomposition; use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2.
        rewrite <- assoc; use cancel_precomposition.
        use monoid_to_unit_left_law.
      Qed.

      Section FixAnInverse.
        Context (inverse : hfiber free_sigma_monoid_adjuction_homset_map f).
        Let h : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧ := pr1 inverse.
        Let hyp : free_sigma_monoid_adjuction_homset_map h = f := pr2 inverse.

        Local Lemma h_respects_τ
          : τ X · pr1 h =
              BinCoproductOfArrows V _ _ (# H (pr1 h)) (pr1 h ⊗^{ Mon_V}_{r} X)
            · BinCoproductArrow (CP (H (pr1 N)) (pr1 N ⊗_{ Mon_V} X)) (SigmaMonoid_τ θ N) (pr1 N ⊗^{ Mon_V}_{l} f 
            · SigmaMonoid_μ θ N).
        Proof.
          use BinCoproductArrowsEq; do 2 rewrite assoc; symmetry; fold (τ' X) (p X).
          - etrans.
            { apply cancel_postcomposition; use BinCoproductOfArrowsIn1. }
            rewrite <- assoc; etrans.
            { apply cancel_precomposition; use BinCoproductIn1Commutes. }
            use (!pr112 h).
          - etrans.
            { apply cancel_postcomposition; use BinCoproductOfArrowsIn2. }
            rewrite <- assoc; etrans.
            { apply cancel_precomposition; use BinCoproductIn2Commutes. }
            rewrite assoc.
            etrans.
            { apply cancel_postcomposition; use (bifunctor_equalwhiskers Mon_V). }
            unfold functoronmorphisms2.
            rewrite <- hyp.
            unfold free_sigma_monoid_adjuction_homset_map.
            do 3 rewrite (bifunctor_leftcomp Mon_V).
            do 2 rewrite <- assoc; etrans.
            { apply cancel_precomposition; rewrite assoc.
              etrans; [| use (pr1 (pr212 h))].
              apply cancel_postcomposition; symmetry.
              apply (bifunctor_equalwhiskers Mon_V). }
            rewrite assoc; use cancel_postcomposition.
            rewrite <- assoc; etrans.
            { apply cancel_precomposition; use (!free_sigma_monoid_ob_compatibility_p X). }
            rewrite <- assoc; etrans.
            { apply cancel_precomposition; do 2 rewrite assoc. 
              rewrite (monoidal_associatorinvnatleftright Mon_V).
              apply cancel_postcomposition; rewrite assoc'.
              apply cancel_precomposition.
              rewrite <- (bifunctor_rightcomp Mon_V).
              apply maponpaths; use monoid_to_unit_right_law. }
            rewrite assoc, assoc, <- id_left.
            use cancel_postcomposition.
            (* Triangle identity *)
            rewrite <- (monoidal_triangleidentity Mon_V), assoc'.
            etrans. 
            { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition. 
              use (pr2 (monoidal_associatorisolaw _ _ _ _)). }
            rewrite id_left, <- (bifunctor_leftcomp Mon_V), <- (bifunctor_leftid Mon_V).
            use maponpaths.
            use (pr2 (monoidal_leftunitorisolaw _ _)).
        Qed.

        Local Definition h' 
          : free_sigma_monoid_ob_initial_monoid_tens_v X --> free_sigma_monoid_adjuction_model.
        Proof.
          refine (pr1 h ,, (_ ,, _) ,, tt); cbn.
          - exact h_respects_τ.
          - exact (pr212 h).
        Defined.
          

        Definition free_sigma_monoid_adjuction_homset_map_weq_unique : h = f'.
        Proof.
          use invmap; [|use path_sigma_hprop|].
          { do 2 try use isapropdirprod.
            - use homset_property.
            - use isaprop_is_monoid_mor.
            - use isapropunit. }
          cbn.
          use (maponpaths pr1 (InitialArrowUnique _ _ h')).
        Qed.

        Definition free_sigma_monoid_adjuction_homset_map_weq_unique_pair
          : inverse  = f',, free_sigma_monoid_adjuction_homset_map_invmap.
        Proof.
          use invmap; [|use path_sigma_hprop|].
          - use homset_property.
          - use free_sigma_monoid_adjuction_homset_map_weq_unique.
        Qed.
      End FixAnInverse.

      Lemma free_sigma_monoid_adjuction_homset_map_weq
        : iscontr (hfiber free_sigma_monoid_adjuction_homset_map f).
      Proof.
        use tpair.
        - exists free_sigma_monoid_adjuction_homset_invmap.
          use free_sigma_monoid_adjuction_homset_map_invmap.
        - use free_sigma_monoid_adjuction_homset_map_weq_unique_pair.
      Defined.

    End FixAMorphism.
  End HomSetMap.

  Lemma free_sigma_monoid_adjuction_homset_weq (X : V) (N : SigmaMonoid θ)
    : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧ ≃ V ⟦ X, forgetful N ⟧.
  Proof.
    exists (free_sigma_monoid_adjuction_homset_map X N).
    intro.
    use free_sigma_monoid_adjuction_homset_map_weq.
  Defined.

  Lemma free_sigma_monoid_adjuction_homset_weq_nat1 (X : V) (N : SigmaMonoid θ) 
    (f : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧) (X' : V) (z : V ⟦ X', X ⟧)
    : free_sigma_monoid_adjuction_homset_weq X' N (# free_sigma_monoid z · f)
    = z · free_sigma_monoid_adjuction_homset_weq X N f.
  Proof.
    cbn; unfold free_sigma_monoid_adjuction_homset_map; cbn.
    do 4 rewrite assoc.
    use cancel_postcomposition.
    rewrite <- monoidal_leftunitorinvnat.
    do 4 rewrite assoc'; use cancel_precomposition.
    rewrite free_sigma_monoid_mor_p, assoc, assoc, assoc.
    use cancel_postcomposition.
    etrans.
    { rewrite <- assoc; apply cancel_precomposition.
      symmetry; use (bifunctor_equalwhiskers Mon_V). }
    unfold functoronmorphisms1; rewrite assoc; etrans.
    { apply cancel_postcomposition; rewrite <- (bifunctor_rightcomp Mon_V); use maponpaths.
      - exact (η X).
      - use (pr2 (pr212 (free_sigma_monoid_mor_init_arrow _ _ z))). }
    use (bifunctor_equalwhiskers Mon_V).
  Qed.

  Lemma free_sigma_monoid_adjuction_homset_weq_nat2 (X : V) (N : SigmaMonoid θ)
    (f : SigmaMonoid θ ⟦ free_sigma_monoid X, N ⟧) 
    (N' : SigmaMonoid θ) (t : SigmaMonoid θ ⟦ N, N' ⟧)
    : free_sigma_monoid_adjuction_homset_weq X N' (f · t) =
      free_sigma_monoid_adjuction_homset_weq X N f · # forgetful t.
  Proof.
    cbn; unfold free_sigma_monoid_adjuction_homset_map; cbn.
    now rewrite assoc.
  Qed.

  Theorem free_sigma_monoid_adjuction
    : are_adjoints free_sigma_monoid forgetful .
  Proof.
    use adj_from_nathomweq; use (_ ,, _ ,, _); hnf.
    - exact free_sigma_monoid_adjuction_homset_weq.
    - exact free_sigma_monoid_adjuction_homset_weq_nat1.
    - exact free_sigma_monoid_adjuction_homset_weq_nat2.
  Defined.
End FreeModelAdjunction.
