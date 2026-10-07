(***************************************************************************

 Free Model Adjunction

 In this file, we define a left-adjoint "Free" to the forgetful functor from
 sigma monoids to the base category.

 On an object X ∈ V, Free gives a sigma monoid whose underlying set is the
 carrier of the initial algebra for (I + H(-) + - ⊗ X).

 Contents
 1. Definitions
 2. Two examples of signatures with strength
 3. Limits are inherited from limits in V
 4. Colimits are inherited from colimits in V

 ***************************************************************************)



Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Chains.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.

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

  Coercion pointed_to_object (X : PtdV) : V := pr1 X.

  Let Mon_PtdV : monoidal PtdV := GeneralizedSubstitutionSystems.Mon_PtdV Mon_V.
  Let Act : actegory Mon_PtdV V:= GeneralizedSubstitutionSystems.Act Mon_V.

  Context (H : V ⟶ V) (θ : pointedtensorialstrength Mon_V H).
  Context (H_omega_cocont : is_omega_cocont H).

  Let forgetful : SigmaMonoid θ ⟶ V 
    := pr1_category _.

  (* Assmuptions on the base monoidal category *)
  Context 
    (O : Initial V)
    (CP : Colims_of_shape two_graph V)
    (CV : Colims_of_shape nat_graph V)
    (left_whiskering_preserves_initial    :  ∏ (v : V), preserves_initial (leftwhiskering_functor Mon_V v))
    (left_whiskering_preserves_coproducts :  ∏ (v : V), 
      preserves_colimits_of_shape (leftwhiskering_functor Mon_V v) two_graph)
    (left_whiskering_omega_cocont         : ∏ (v : V), is_omega_cocont (leftwhiskering_functor Mon_V v))
    (right_whiskering_omega_cocont        : ∏ (v : V), is_omega_cocont (rightwhiskering_functor Mon_V v)).

  Local Definition H_omega_sig_strength
    : pointedtensorialstrength_omega_cocont_cat Mon_V
    := (H ,, θ) ,, H_omega_cocont.

  Local Lemma tens_functor_eq (v : V)
    : product_signature_functor Mon_V (functor_identity V) v = rightwhiskering_functor Mon_V v.
  Proof.
    use functor_eq.
    { use homset_property. }
    use functor_data_eq; easy.
  Qed.

  Local Definition tens_omega_sig_strength (v : V)
    : pointedtensorialstrength_omega_cocont_cat Mon_V.
  Proof.
    exists (_ ,, 
      product_signature_strength Mon_V (functor_identity V) 
        (trivial_signature_with_strength Mon_V) v).
    abstract (
      cbn;
      rewrite tens_functor_eq;
      use right_whiskering_omega_cocont
    ).
  Defined.

  Local Definition H_tens_omega_sig_strength (v : V)
    : pointedtensorialstrength_omega_cocont_cat Mon_V.
  Proof.
    eapply colim.
    use (omega_signature_with_strength_inherits_colimits _ _ _ _
      (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v))).
    - use CP.
    - use left_whiskering_preserves_coproducts.
  Defined.

  Local Definition H̃ v
    : V ⟶ V
    := (pr11 (H_tens_omega_sig_strength v)).

  Local Definition θ̃ v
    : pointedtensorialstrength Mon_V (H̃ v)
    := (pr21 (H_tens_omega_sig_strength v)).

  Local Definition δ
    : bifunctor_bincoprod_distributor
      (Limits.BinCoproducts.BinCoproducts_from_Colims V CP)
      (Limits.BinCoproducts.BinCoproducts_from_Colims V CP) Act.
  Proof.
    use tpair.
    - intros [a pt_a] b c; use (colimArrow (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ (pr2 (CP _))))).
      use make_cocone; [intros [|]|]; cbn.
      + use (colimIn (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) true).
      + use (colimIn (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) false).
      + abstract (intros _ _ []).
    - abstract (
        intros [a pt_a] b c;
        split; cbn;
        [
          symmetry;
          use (colim_endo_is_identity _ (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ (pr2 (CP _)))));
          intros [|]; cbn;
          [
            rewrite assoc;
            etrans;
            [ apply cancel_postcomposition;
              use (colimArrowCommutes (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ 
                (pr2 (CP (Limits.BinCoproducts.bincoproduct_diagram V b c))))) _ _ true) |];
              use (colimArrowCommutes (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) _ _ true)
          |
            rewrite assoc;
            etrans;
            [ apply cancel_postcomposition;
              use (colimArrowCommutes (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ 
                (pr2 (CP (Limits.BinCoproducts.bincoproduct_diagram V b c))))) _ _ false) |];
            use (colimArrowCommutes (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) _ _ false)
        ]
      |
        symmetry; use colim_endo_is_identity; intros [|]; cbn;
        [
          rewrite assoc;
          etrans;
          [ apply cancel_postcomposition;
            use (colimArrowCommutes (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) _ _ true) |];
          use (colimArrowCommutes (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ (pr2 (CP (Limits.BinCoproducts.bincoproduct_diagram V b c))))) _ _ true)
        |
          rewrite assoc;
          etrans;
          [ apply cancel_postcomposition;
            use (colimArrowCommutes (CP (Limits.BinCoproducts.bincoproduct_diagram V (a ⊗_{ Mon_V} b) (a ⊗_{ Mon_V} c))) _ _ false) |];
          use (colimArrowCommutes (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ (pr2 (CP (Limits.BinCoproducts.bincoproduct_diagram V b c))))) _ _ false)
        ]
      ]
    ).
  Defined.

  Opaque SigmaMonoidFromInitialAlgebraInitial.

  Local Definition H_tens_initial_model (v : V)
    : Initial (SigmaMonoid (θ̃ v)).
  Proof.
    use SigmaMonoidFromInitialAlgebraInitial.
    - now use Limits.BinCoproducts.BinCoproducts_from_Colims.
    - use δ.
    - use O.
    - use CV.
    - use (pr2 (H_tens_omega_sig_strength v)).
    - intro w; use (left_whiskering_preserves_initial w _ (pr2 O)).
    - use left_whiskering_omega_cocont.
  Qed.

  Local Definition ΣM v : SigmaMonoid (θ̃ v) := H_tens_initial_model v.
  Local Definition M v : V := SigmaMonoid_carrier _ (ΣM v).
  Local Definition Mon v : monoid Mon_V (M v) := pr2 (SigmaMonoid_to_monoid _ (ΣM v)).
  Local Definition η v : V⟦I_{Mon_V}, M v⟧ := SigmaMonoid_η _ (ΣM v).
  Local Definition μ v : V⟦M v ⊗_{Mon_V} M v, M v⟧ := SigmaMonoid_μ _ (ΣM v).
  Local Definition τ v : V⟦H (M v), M v⟧ := colimIn (CP _) true · SigmaMonoid_τ _ (ΣM v).
  Local Definition σ v : V⟦M v ⊗_{Mon_V} v, M v⟧ := colimIn (CP _) false · SigmaMonoid_τ _ (ΣM v).

  Local Lemma σ_is_module_mor (v : V)
    : αinv^{Mon_V}_{_,_,_} · μ v ⊗^{Mon_V}_{r} v · σ v 
      = M v ⊗^{Mon_V}_{l} σ v · μ v.
  Proof.
    pose (d m := (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _) 
        (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v)))) m)).
    use pathsinv0.
    etrans.
    { unfold σ; rewrite (bifunctor_leftcomp Mon_V), <- assoc.
      apply cancel_precomposition.
      use pathsinv0.
      use SigmaMonoid_is_compatible. }
    cbn; do 2 rewrite assoc.
    etrans.
    { do 2 apply cancel_postcomposition.
      unfold colimit_sig_strength_data; unfold colimOfArrows.
      use (colimArrowCommutes
            (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts (M v) _ _ _ (pr2 (CP (d (M v))))))
        _ _ false
      ). }
    cbn; unfold product_signature_strength_mor; cbn.
    do 2 rewrite <- assoc.
    etrans.
    { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition.
      use (colimOfArrowsIn _ _ (CP (d (M v ⊗_{Mon_V} M v))) (CP (d (M v))) _ _ false). }
    cbn.
    do 2 rewrite assoc; rewrite <- assoc; do 2 use cancel_postcomposition.
    rewrite <- id_right; use cancel_precomposition.
    use (bifunctor_rightid Mon_V). 
  Qed.

  Local Lemma HM_v_compatible (v : V)
    : θ (M v,, η v) (M v) · # H (μ v) · τ v
      = M v ⊗^{ Mon_V}_{l} τ v · μ v.
  Proof.
    pose (d m := (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _) 
        (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v)))) m)).
    use pathsinv0.
    etrans.
    { unfold τ; rewrite (bifunctor_leftcomp Mon_V), <- assoc.
      apply cancel_precomposition.
      use pathsinv0.
      use SigmaMonoid_is_compatible. }
    cbn; do 2 rewrite assoc.
    etrans.
    { do 2 apply cancel_postcomposition.
      unfold colimit_sig_strength_data; unfold colimOfArrows.
      use (colimArrowCommutes
            (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts (M v) _ _ _ (pr2 (CP (d (M v))))))
        _ _ true
      ). }
    cbn; unfold product_signature_strength_mor; cbn.
    do 2 rewrite <- assoc.
    etrans.
    { apply cancel_precomposition; rewrite assoc; apply cancel_postcomposition.
      use (colimOfArrowsIn _ _ (CP (d (M v ⊗_{Mon_V} M v))) (CP (d (M v))) _ _ true). }
    cbn.
    do 2 rewrite assoc; now rewrite <- assoc.
  Qed.

  Local Definition HM (v : V) : SigmaMonoid θ.
  Proof.
    exists (M v).
    exists (τ v ,, Mon v).
    use HM_v_compatible.
  Defined.

  Local Definition ν v : V⟦v, M v⟧ := luinv^{Mon_V}_{v} · η v ⊗^{Mon_V}_{r} v · σ v.

  Local Lemma σ_with_ν (v : V) : σ v = (M v ⊗^{Mon_V}_{l} ν v) · μ v.
  Proof.
    use pathsinv0; unfold ν; do 2 rewrite (bifunctor_leftcomp Mon_V).
    etrans.
    { rewrite <- assoc; apply cancel_precomposition.
      use (!σ_is_module_mor v). }
    do 2 rewrite assoc.
    rewrite <- id_left; apply cancel_postcomposition.
    etrans.
    { do 2 rewrite <- assoc; apply cancel_precomposition.
      rewrite assoc; apply cancel_postcomposition.
      use monoidal_associatorinvnatleftright. }
    do 2 rewrite assoc; rewrite <- assoc.
    etrans.
    { apply cancel_precomposition.
      rewrite <- (bifunctor_rightcomp Mon_V).
      apply maponpaths.
      use (monoid_to_unit_right_law Mon_V (Mon v)). }
    rewrite (monoidal_triangle_identity_inv Mon_V).
    rewrite <- (bifunctor_rightcomp Mon_V), <- (bifunctor_rightid Mon_V).
    use maponpaths.
    use is_inverse_in_precat2.
    use (monoidal_rightunitorisolaw Mon_V).
  Qed.

  Section UniversalProperty.
    Context (v : V).
    Context (M : SigmaMonoid θ).

    Let m := SigmaMonoid_carrier _ M.
    Let μM := SigmaMonoid_μ _ M.
    Let ηM := SigmaMonoid_η _ M.

    Context (f : V⟦v, m⟧).

    Let s : V⟦m ⊗_{Mon_V} v, m⟧ := m ⊗^{Mon_V}_{l} f · μM.

    Local Definition s_is_module_mor
      : m ⊗^{Mon_V}_{l} s · μM = αinv^{Mon_V}_{_,_,_} · μM ⊗^{Mon_V}_{r} v · s.
    Proof.
      assert (α^{Mon_V}_{_,_,_} · m ⊗^{Mon_V}_{l} s · μM = μM ⊗^{Mon_V}_{r} v · s) as hyp.
      { 
        unfold s; rewrite (bifunctor_leftcomp Mon_V), assoc, assoc.
        rewrite monoidal_associatornatleft.
        etrans.
        { do 2 rewrite <- assoc; apply cancel_precomposition.
          rewrite assoc; use monoid_to_assoc_law. }
        rewrite assoc.
        use cancel_postcomposition.
        do 2 rewrite (@tensor_mor_left V_Mon), (@tensor_mor_right V_Mon).
        etrans.
        { use pathsinv0; use (@tensor_split V_Mon). }
        use (@tensor_split' V_Mon). 
      }
      symmetry; rewrite <- id_left.
      rewrite <- assoc, <- hyp, assoc, assoc, assoc.
      do 2 use cancel_postcomposition.
      use is_inverse_in_precat2.
      use (monoidal_associatorisolaw Mon_V).
    Qed.

    Local Definition model_of_H̃_without_compatibility
      : total_category (@SigmaMonoid_disp_cat_no_compatibility V Mon_V (H̃ v)).
    Proof.
      exists m; use tpair.
      - use colimArrow; use make_cocone; [intros [|]|]; cbn.
        + use SigmaMonoid_τ.
        + use s.
        + abstract (intros ? ? []).
      - use (pr2 (SigmaMonoid_to_monoid _ M)).
    Defined.

    Local Lemma model_of_H̃_compatibility
      : SigmaMonoid_compatibility (θ̃ v) model_of_H̃_without_compatibility.
    Proof.
      pose (d m := (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _) 
          (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v)))) m)).
      use (colimArrowUnique' (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts _ _ _ _ (pr2 (CP _))))).
      intros [|]; cbn.
      - do 3 rewrite assoc.
        etrans.
        { do 2 apply cancel_postcomposition.
          unfold colimit_sig_strength_data.
          unfold colimOfArrows.
          use (colimArrowCommutes
                (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts m _ _ _ (pr2 (CP (d m)))))
            _ _ true
          ). }
        cbn.
        etrans.
        { do 2 rewrite <- assoc; apply cancel_precomposition.
          rewrite assoc; apply cancel_postcomposition.
          unfold ColimFunctor_mor; cbn.
          use (colimOfArrowsIn _ _ (CP (d (m ⊗_{ Mon_V} m))) (CP (d m)) _ _ true). }
        cbn; do 2 rewrite assoc; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use (colimArrowCommutes (CP (d m)) _ _ true). }
        cbn.
        symmetry.
        rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths.
          use (colimArrowCommutes (CP (d m)) _ _ true). }
        cbn.
        symmetry.
        use SigmaMonoid_is_compatible.
      - do 3 rewrite assoc.
        etrans.
        { do 2 apply cancel_postcomposition.
          unfold colimit_sig_strength_data.
          unfold colimOfArrows.
          use (colimArrowCommutes
                (make_ColimCocone _ _ _ (left_whiskering_preserves_coproducts m _ _ _ (pr2 (CP (d m)))))
            _ _ false
          ). }
        cbn.
        etrans.
        { do 2 rewrite <- assoc; apply cancel_precomposition.
          rewrite assoc; apply cancel_postcomposition.
          unfold ColimFunctor_mor; cbn.
          use (colimOfArrowsIn _ _ (CP (d (m ⊗_{ Mon_V} m))) (CP (d m)) _ _ false). }
        cbn; do 2 rewrite assoc; rewrite <- assoc.
        etrans.
        { apply cancel_precomposition; use (colimArrowCommutes (CP (d m)) _ _ false). }
        cbn.
        symmetry.
        rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { apply cancel_postcomposition; apply maponpaths.
          use (colimArrowCommutes (CP (d m)) _ _ false). }
        unfold product_signature_strength_mor; cbn.
        refine (s_is_module_mor @ !_).
        do 2 use cancel_postcomposition; rewrite <- id_right; use cancel_precomposition.
        use (bifunctor_rightid Mon_V).
    Qed.

    Local Definition model_of_H̃ 
      : SigmaMonoid (θ̃ v).
    Proof.
      do 2 eexists; exact model_of_H̃_compatibility.
    Defined.

    Local Definition model_of_H̃_arrow
      : SigmaMonoid (θ̃ v) ⟦ ΣM v , model_of_H̃ ⟧.
    Proof.
      use InitialArrow.
    Defined.

    Local Definition universal_arrow
      : SigmaMonoid θ ⟦ HM v , M ⟧.
    Proof.
      exists (pr1 model_of_H̃_arrow).
      use ((_ ,, _) ,, tt); cbn.
      - abstract (
          unfold τ;
          etrans; 
          [rewrite <- assoc; apply cancel_precomposition; use (pr112 model_of_H̃_arrow)|];
          cbn; unfold ColimFunctor_mor; rewrite assoc;
          etrans;
          [apply cancel_postcomposition;
            use (colimOfArrowsIn _ _ (CP 
              (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _)
                    (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v))))
              (pr1 (ΣM v)))) _ _ _ true) |];
          cbn; rewrite <- assoc; use cancel_precomposition;
          use (colimArrowCommutes (CP (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _)
                  (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v))))
                m)) _ _ true)
        ).
      - exact (pr212 model_of_H̃_arrow).
    Defined.

    Local Definition universal_arrow_property
      : ν v · # (pr1_category _) universal_arrow = f.
    Proof.
      unfold ν, σ; rewrite assoc.
      etrans.
      { do 2 rewrite <- assoc; do 2 apply cancel_precomposition.
        exact (pr112 model_of_H̃_arrow). }
      etrans.
      { apply cancel_precomposition; rewrite assoc; cbn.
        etrans.
        { apply cancel_postcomposition.
          use (colimOfArrowsIn _ _ (CP 
              (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _)
                    (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v))))
              (pr1 (ΣM v)))) _ _ _ false). }
        cbn.
        rewrite <- assoc.
        apply cancel_precomposition.
        use (colimArrowCommutes (CP (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _)
                  (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v))))
                m)) _ _ false). }
      cbn; rewrite assoc.
      unfold s.
      etrans.
      { do 2 rewrite <- assoc; apply cancel_precomposition.
        rewrite assoc; apply cancel_postcomposition.
        rewrite <- (bifunctor_rightcomp Mon_V); use maponpaths.
        - exact ηM.
        - exact (pr2 (pr212 model_of_H̃_arrow)). }
      do 2 rewrite assoc.
      etrans.
      { apply cancel_postcomposition; rewrite <- assoc.
        apply cancel_precomposition.
        use (bifunctor_equalwhiskers Mon_V). }
      unfold functoronmorphisms2.
      do 2 rewrite <- assoc.
      etrans.
      { do 2 apply cancel_precomposition; use monoid_to_unit_left_law. }
      rewrite (monoidal_leftunitornat Mon_V), assoc, <- id_left.
      use cancel_postcomposition.
      use is_inverse_in_precat2.
      use monoidal_leftunitorisolaw.
    Qed.

    Local Definition universal_arrow_unique
      (g : SigmaMonoid θ ⟦ HM v , M ⟧)
      (g_hyp : ν v · # forgetful g = f)
      : g = universal_arrow.
    Proof.
      pose (g' := #forgetful g).
      use SigmaMonoid_mor_eq.
      assert (σ v · g' = g' ⊗^{Mon_V}_{r} v · s) as hyp.
      { rewrite σ_with_ν.
        etrans.
        { rewrite <- assoc; use cancel_precomposition.
          - exact (g' ⊗^{Mon_V} g' · μM).
          - exact (!pr1 (pr212 g)). }
        etrans.
        { apply cancel_precomposition; apply cancel_postcomposition.
          use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2; do 2 rewrite assoc.
        rewrite <- (bifunctor_leftcomp Mon_V).
        etrans.
        { do 2 apply cancel_postcomposition; apply maponpaths; use g_hyp. }
        unfold s.
        rewrite assoc.
        use cancel_postcomposition.
        symmetry.
        use (bifunctor_equalwhiskers Mon_V). }

      unfold universal_arrow; cbn; unfold model_of_H̃_arrow.

      transparent assert (g'' : (SigmaMonoid (θ̃ v) ⟦ H_tens_initial_model v, model_of_H̃ ⟧)).
      { use (g' ,, (_ ,, _) ,, tt); [|use (pr212 g)]; cbn.
        abstract (
          pose (d m := (diagram_pointwise (mapdiagram (pr1_category _) (mapdiagram (pr1_category _) 
              (bincoproduct_diagram H_omega_sig_strength (tens_omega_sig_strength v)))) m));
          use colimArrowUnique'; intros [|]; cbn; apply pathsinv0;
          [
            rewrite assoc;
            etrans;
            [apply cancel_postcomposition; use (colimOfArrowsIn _ _ (CP (d _)) _ _ _ true)|];
            cbn; rewrite <- assoc;
            etrans;
            [apply cancel_precomposition; use (colimArrowCommutes (CP (d _)) _ _ true)|];
            cbn;
            rewrite assoc;
            exact (!pr112 g)
          |
            rewrite assoc;
            etrans;
            [apply cancel_postcomposition; use (colimOfArrowsIn _ _ (CP (d _)) _ _ _ false)|];
            cbn; rewrite <- assoc;
            etrans;
            [apply cancel_precomposition; use (colimArrowCommutes (CP (d _)) _ _ false)|];
            cbn;
            rewrite assoc;
            exact (!hyp)
          ]
        ).
      }
      cbn.
      use (maponpaths pr1 (InitialArrowUnique (H_tens_initial_model v) _ g'')).
    Qed.
  End UniversalProperty.

  Opaque universal_arrow.

  Lemma universal_property_of_free_models
    (v : V)
    (M : SigmaMonoid θ)
    (f : V⟦v, SigmaMonoid_carrier _ M⟧)
    : ∃! f' : SigmaMonoid θ⟦HM v, M⟧, ν v · #forgetful f' = f.
  Proof.
    use unique_exists.
    - now use universal_arrow.
    - use universal_arrow_property.
    - abstract (intro; use homset_property).
    - use universal_arrow_unique.
  Defined.

  Definition free_model_functor_data
    : functor_data V (SigmaMonoid θ).
  Proof.
    use make_functor_data.
    - exact HM.
    - intros v v' f; use universal_arrow; exact (f · ν v').
  Defined.

  Lemma free_model_functor_is_functor
    : is_functor free_model_functor_data.
  Proof.
    split.
    - intro a.
      use pathsinv0.
      use universal_arrow_unique.
      now cbn; rewrite id_left, id_right.
    - intros a b c f g.
      use pathsinv0.
      use universal_arrow_unique.
      simpl; rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        use (universal_arrow_property _ (HM _)). }
      do 2 rewrite <- assoc; apply cancel_precomposition.
      use (universal_arrow_property _ (HM _)).
  Qed.

  Definition free_model_functor
    : V ⟶ SigmaMonoid θ
    := free_model_functor_data ,, free_model_functor_is_functor.

  Definition free_model_adjunction_unit
    : functor_identity V ⟹ free_model_functor ∙ forgetful.
  Proof.
    use make_nat_trans.
    - use ν. 
    - abstract (intros ? ? ?; use pathsinv0; use (universal_arrow_property _ (HM _))).
  Defined.

  Definition free_model_adjunction_counit
    : forgetful ∙ free_model_functor ⟹ functor_identity (SigmaMonoid θ).
  Proof.
    use make_nat_trans.
    - intro M; use universal_arrow; use identity.
    - abstract (
        intros M M' f;
        use (universal_arrow_unique _ _ _ _ _ @ !universal_arrow_unique _ _ _ _ _);
        [
          use (#forgetful f)
        |
          cbn; rewrite assoc; etrans;
          [apply cancel_postcomposition;use (universal_arrow_property _ (HM _))|];
          rewrite <- id_right, <- assoc; apply cancel_precomposition; use universal_arrow_property
        | cbn; rewrite assoc, <- id_left;
          use cancel_postcomposition; use universal_arrow_property
        ]
    ).
  Defined.

  Opaque SigmaMonoid.

  Lemma free_model_adjunction_law
    : form_adjunction free_model_functor forgetful free_model_adjunction_unit free_model_adjunction_counit.
  Proof.
    use make_form_adjunction.
    - intro v; cbn.
      etrans.
      use universal_arrow_unique.
      + exact (ν v).
      + rewrite functor_comp, assoc.
        etrans.
        { apply cancel_postcomposition; use (universal_arrow_property _ (HM _)). }
        rewrite <- id_right, <- assoc; apply cancel_precomposition.
        use universal_arrow_property.
      + symmetry; use universal_arrow_unique; now rewrite functor_id, id_right.
    - intro M; use universal_arrow_property.
  Qed.

  Transparent SigmaMonoid.

  Theorem free_model_adjunction
    : is_right_adjoint forgetful.
  Proof.
    exists free_model_functor.
    use make_are_adjoints.
    - exact free_model_adjunction_unit.
    - exact free_model_adjunction_counit.
    - exact free_model_adjunction_law.
  Defined.
End FreeModelAdjunction.
