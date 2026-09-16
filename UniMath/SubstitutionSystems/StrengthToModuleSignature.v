(***************************************************************************

   Strength to module signature

   In this file, we define a functor from the category of signatures with a
   pointed tensorial strength to module signatures, and prove it maps simple
   examples of signatures with strength to the expected module signatures.
   Finally, we show that models for the obtained module signatures are
   equivalent to Sigma monoids.

 Contents
 1. Definitions
 2. Mapping of trivial and product signatures
 3. Mapping of constructred limits and colimits of signatures
 4. Models are Sigma monoids
 5. Instance where the functor is not essentially surjective

 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* Require Import UniMath.Tactics.EnsureStructuredProofs. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.ModelsOfModuleSignature.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.

Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.SubstitutionSystems.CategoryOfSignaturesWithStrength.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section StrengthToModuleSignature.
  Context {V : category} (Mon_V : monoidal V).

  Let V_Mon : monoidal_cat := V ,, Mon_V.

  Local Definition PtdV : category := coslice_cat_total V I_{Mon_V}.
  Local Definition Mon_PtdV : monoidal PtdV := monoidal_pointed_objects Mon_V.

  Local Definition Mon_V_swapped : monoidal V := monoidal_swapped Mon_V.

  (** 1. Definitions *)

  Section FixAStrength.
    Context {H : V ⟶ V}.
    Context (θ : pointedtensorialstrength Mon_V_swapped H).

    Local Definition monoid_to_pointed (R : MON Mon_V) : PtdV
      := pr1 R ,, monoid_data_unit _ (pr12 R).

    Section FixAMonoid.
      Context (R : MON Mon_V).

      Let R_ob : V := monoid_carrier _ R.
      Let η : I_{Mon_V} --> R_ob := monoid_data_unit _ (pr12 R).
      Let μ : R_ob ⊗_{Mon_V} R_ob --> R_ob := monoid_data_multiplication _ (pr12 R).

      Let pointed_R : PtdV := monoid_to_pointed R.
      Let pointed_RR : PtdV := pointed_R ⊗_{Mon_PtdV} pointed_R.

      Local Definition pointed_monoid_unit : PtdV ⟦ I_{Mon_PtdV}, pointed_R ⟧
        := η ,, id_left _.

      Local Lemma pointed_multiplication_lemma
        : luinv^{_}_{_} · η ⊗^{Mon_V} η · μ = η.
      Proof.
        etrans.
        { refine (maponpaths (λ x, _ · x · _) _); use (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms2.
        rewrite assoc, (monoidal_leftunitorinvnat Mon_V), <- id_right, <- assoc, <- assoc.
        refine (maponpaths _ _).
        etrans.
        { refine (maponpaths _ _); use monoid_to_unit_left_law. }
        use (pr2 (monoidal_leftunitorisolaw _ _)).
      Qed.

      Local Definition pointed_multiplication : PtdV ⟦ pointed_RR, pointed_R ⟧
        := μ ,, pointed_multiplication_lemma.

      Let HR_module_subst : H R_ob ⊗_{Mon_V} R_ob --> H R_ob
        := θ pointed_R R_ob · #H μ.

      Local Lemma HR_module_subst_assoc
        : module_laws_assoc (C := V_Mon) (pr1 R) (pr2 R) HR_module_subst.
      Proof.
        unfold module_laws_assoc, HR_module_subst.
        do 2 rewrite assoc; rewrite (bifunctor_rightcomp Mon_V).
        unfold RModules.μ; fold μ R_ob.
        symmetry; etrans.
        { refine (maponpaths (λ x, x · _) _); rewrite <- assoc; refine (maponpaths _ _).
          use (lineator_linnatleft _ _ _ _ θ pointed_R). }
        cbn; rewrite assoc.
        etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use (!monoid_to_assoc_law _ _). }
        do 2 rewrite functor_comp, assoc.
        symmetry; etrans.
        { do 2 rewrite <- assoc; refine (maponpaths _ _).
          rewrite assoc; refine (maponpaths (λ x, x · _) _).
          use (lineator_linnatright _ _ _ _ θ _ _ _ pointed_multiplication). }
        cbn; do 2 rewrite assoc; refine (!maponpaths (λ x, x · _ · _) _).
        symmetry; rewrite <- id_left, assoc, assoc, <- (pr1 (monoidal_associatorisolaw _ _ _ _)); symmetry.
        etrans.
        { refine (maponpaths (λ x, x · _) _); do 2 rewrite <- assoc.
          refine (maponpaths _ _); rewrite assoc.
          symmetry; rewrite <- id_left, assoc, assoc; symmetry.
          etrans; [refine (!maponpaths (λ x, x · _ · _ · _) _); use (tensor_id_id (V := V_Mon)) |].
          rewrite <- tensor_mor_left.
          use (!lineator_preservesactor _ _ _ _ θ pointed_R pointed_R _). }
        cbn; unfold reindexed_actor_data; cbn.
        rewrite <- assoc, <- assoc; use maponpaths.
        rewrite unitorsinv_coincide_on_unit, functor_comp, assoc, assoc.
        etrans.
        { refine (maponpaths (λ x, _ · x · _ · _) _).
          now rewrite (tensor_mor_left (V := V_Mon)), (tensor_id_id (V := V_Mon)), functor_id. }
        rewrite id_right; etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use (pr2 (monoidal_associatorisolaw _ _ _ _)). }
        eassert (_ ⊗^{ tensor_swapped Mon_V} _ = _ ⊗^{Mon_V} _) as hyp
        by use monoidal_swapped_whiskering.
        now rewrite functor_id, id_right, hyp.
      Qed.

      Local Lemma HR_module_subst_unit
        : module_laws_unit (C := V_Mon) (pr1 R) (pr2 R) HR_module_subst.
      Proof.
        unfold module_laws_unit, HR_module_subst, RModules.η; cbn.
        rewrite assoc; etrans.
        { refine (maponpaths (λ x, x · _) _); use (lineator_linnatright _ _ _ _ θ _ _ _ pointed_monoid_unit). }
        cbn; etrans.
        { rewrite <- assoc, <- functor_comp; do 2 refine (maponpaths _ _).
          use monoid_to_unit_right_law. }
        rewrite <- id_left; etrans.
        2: { refine (maponpaths (λ x, x · _) _); use (tensor_id_id (V := V_Mon)). }
        rewrite <- tensor_mor_left.
        etrans; [|use (lineator_preservesunitor _ _ _ _ θ)].
        cbn; do 2 use maponpaths.
        symmetry; rewrite <- id_left.
        use (maponpaths (λ x, x · _) _); cbn.
        now rewrite (tensor_mor_left (V := V_Mon)), (tensor_id_id (V := V_Mon)).
      Qed.

      Definition strength_to_module
        : module (C := V_Mon) R_ob (monoid_struct _ R) (H R_ob)
        := make_module _ _ _ HR_module_subst_unit HR_module_subst_assoc.
    End FixAMonoid.

    (* Functoriality *)
    Section FixAMonoidMorphism.
      Context (R R' : MON Mon_V) (r : R --> R').

      Let R_ob  : V := monoid_carrier _ R.
      Let R'_ob : V := monoid_carrier _ R'.
      Let r_ob : R_ob --> R'_ob := pr1 r.

      Local Definition r_as_pointed_morphism
        : monoid_to_pointed R --> monoid_to_pointed R'
        := r_ob ,, pr22 r.

      Lemma strength_to_module_morphism
        : is_module_mor _ _ (strength_to_module R)
          (pullback_functor_funct _ (strength_to_module R') _ (pr2 r)) (#H r_ob).
      Proof.
        unfold is_module_mor, pullback_functor_funct; cbn.
        do 2 rewrite assoc.
        etrans.
        2: { rewrite <- assoc, <- functor_comp. refine (maponpaths (λ x, _ · #H x ) (pr12 r)). }
        rewrite functor_comp, assoc; refine (maponpaths (λ x, x · _) _).
        fold R'_ob R_ob r_ob.
        unfold functoronmorphisms1; rewrite functor_comp, assoc.
        etrans.
        { rewrite <- assoc; refine (maponpaths _ (lineator_linnatright _ _ _ _ θ _ _ _ r_as_pointed_morphism)). }
        cbn; rewrite assoc; use (maponpaths (λ x, x · _) _).
        use (lineator_linnatleft _ _ _ _ θ (monoid_to_pointed R)).
      Qed.
    End FixAMonoidMorphism.

    Definition strength_to_module_signature_data
      : @module_signature_data V_Mon.
    Proof.
      use tpair.
      - exact (λ R, _ ,, strength_to_module R).
      - exact (λ R R' r, _ ,, strength_to_module_morphism _ _ r).
    Defined.

    Lemma strength_to_module_signature_axioms
      : module_signature_axioms strength_to_module_signature_data.
    Proof.
      split; intros; apply MOD_mor_eq.
      - use functor_id.
      - use functor_comp.
    Qed.

    Definition strength_to_module_signature
      : module_signature_cat
      := strength_to_module_signature_data ,, strength_to_module_signature_axioms.
  End FixAStrength.

  Section FixAStrengthMorphism.
    Context {H H' : V ⟶ V} {α : H ⟹ H'}.
    Context {θ : pointedtensorialstrength Mon_V_swapped H}.
    Context {θ' : pointedtensorialstrength Mon_V_swapped H'}.
    Context (hyp : is_linear_nat_trans θ θ' α).

    Lemma strength_to_module_signature_morphism_lemma
      (R : MON Mon_V)
      : α (monoid_carrier Mon_V R) ⊗^{ Mon_V}_{r} pr1 R
        · H' (monoid_carrier Mon_V R) ⊗^{ Mon_V}_{l} identity (pr1 R)
        · θ' (monoid_to_pointed R) (monoid_carrier Mon_V R)
        · # H' (monoid_data_multiplication Mon_V (pr12 R))
      = θ (monoid_to_pointed R) (monoid_carrier Mon_V R)
        · # H (monoid_data_multiplication Mon_V (pr12 R))
        · α (monoid_carrier Mon_V R).
    Proof.
      rewrite (bifunctor_leftid Mon_V), id_right.
      etrans.
      2: { rewrite <- assoc; refine (!maponpaths _ _); use nat_trans_ax. }
      cbn; rewrite assoc; use (!maponpaths (λ x, x · _) _).
      use (hyp (monoid_to_pointed R)).
    Qed.

    Definition strength_to_module_signature_morphism
      : strength_to_module_signature θ --> strength_to_module_signature θ'.
    Proof.
      use tpair; cbn.
      - intros R; exists (α _); cbn.
        abstract (
            unfold is_module_mor; cbn;
            do 2 rewrite assoc;
            use strength_to_module_signature_morphism_lemma
          ).
      - intros R R' f; apply MOD_mor_eq.
        abstract (unfold mor_disp; cbn;
             rewrite transportf_total2; cbn;
             rewrite transportf_const; cbn;
             use nat_trans_ax
          ).
    Defined.
  End FixAStrengthMorphism.

  Definition strength_to_module_signature_functor_data
    : functor_data (pointedtensorialstrength_cat Mon_V_swapped) (module_signature_cat (C := V_Mon)).
  Proof.
    use tpair.
    - intros [? θ]; exact (strength_to_module_signature θ).
    - intros ? ? [? hyp]; exact (strength_to_module_signature_morphism hyp).
  Defined.

  Lemma strength_to_module_signature_functor_laws
    : is_functor strength_to_module_signature_functor_data.
  Proof.
    split.
    - intro. apply section_nat_trans_eq; intro.
      apply MOD_mor_eq; easy.
    - intros ? ? ? ? ?. apply section_nat_trans_eq; intro.
      apply MOD_mor_eq. cbn; unfold mor_disp.
      cbn; rewrite transportf_total2.
      cbn; now rewrite transportf_const.
  Qed.

  Definition strength_to_module_signature_functor
    : pointedtensorialstrength_cat Mon_V_swapped ⟶ module_signature_cat (C := V_Mon)
    := make_functor _ strength_to_module_signature_functor_laws.


  (** 2. Mapping of trivial and product signatures *)

  (* The functor maps the "trivial" and "product" signatures with strength to *)
  (* their equivalent as module signatures                                    *)

  Proposition signature_with_strength_to_module_signatures_trivial
    : strength_to_module_signature (trivial_signature_with_strength Mon_V_swapped)
      = trivial_signature.
  Proof.
    use module_signature_equality.
    - intro. use total2_paths_f.
      + use idpath.
      + abstract (
          use subtypePath;
          [use isaprop_module_laws|use id_left]
        ).
    - intros; etrans.
      + refine (maponpaths _ _); use transportf_total2_paths_f.
      + use (transportf_total2_paths_f (λ x, x --> _)).
  Qed.

  Proposition signature_with_strength_to_module_signatures_product
    (H : V ⟶ V) (θ : pointedtensorialstrength Mon_V_swapped H) (D : V)
    : strength_to_module_signature (product_signature_strength Mon_V_swapped H θ D)
      = product_signature (strength_to_module_signature θ) D.
  Proof.
    use module_signature_equality.
    - intro; use total2_paths_f.
      + use idpath.
      + abstract (
        use subtypePath;
        [ use isaprop_module_laws
        | cbn; unfold product_module_subst; cbn; now rewrite (bifunctor_leftcomp Mon_V), assoc ]
          ).
    - intros; etrans.
      + refine (maponpaths _ _); use transportf_total2_paths_f.
      + use (transportf_total2_paths_f (λ x, x --> _)).
  Qed.

  (** 3. Mapping of constructred limits and colimits of signatures *)

  (* The functor maps the constructions for (co)limits signatures with strength *)
  (* to the equivalent construction as module signatures                        *)

  Local Lemma tens_swapped {g : graph}
    (tens_R : ∏ R, preserves_colimits_of_shape (rightwhiskering_functor Mon_V R) g)
    : ∏ A, preserves_colimits_of_shape (leftwhiskering_functor Mon_V_swapped A) g.
  Proof.
    intro A.
    assert (rightwhiskering_functor Mon_V A = leftwhiskering_functor Mon_V_swapped A)
    by (use functor_eq; [use homset_property|reflexivity]).
    now use (transportf (λ x, preserves_colimits_of_shape x g) _ (tens_R A)).
  Qed.

  Proposition signature_with_strength_to_module_signatures_colimits (g : graph)
    (colims_V : Colims_of_shape g V)
    (tens_R : ∏ R, preserves_colimits_of_shape (rightwhiskering_functor Mon_V R) g)
    (d : diagram g (pointedtensorialstrength_cat Mon_V_swapped))
    : strength_to_module_signature_functor (colimit_signature_with_strength _ colims_V (λ x, tens_swapped tens_R (pr1 x)) d)
    = colimit_module_signature (mapdiagram strength_to_module_signature_functor d) colims_V (λ x, tens_swapped tens_R (pr1 x)).
  Proof.
    use module_signature_equality.
    - intro R; use total2_paths_f.
      + use idpath.
      + abstract (
        use subtypePath;
        [use isaprop_module_laws|];
        cbn;
        unfold colimit_sig_strength_data, ColimFunctor_mor, colim_module_subst;
        use (colimArrowUnique' (ColimCocone_L_R _ (pr2 R) _ _ _));
        intro u;
        etrans;
        [rewrite assoc; apply cancel_postcomposition;
          use (colimOfArrowsIn _ _ (ColimCocone_L_R _ (pr2 R) _ _ _))|];
        cbn; etrans;
        [rewrite <- assoc; apply cancel_precomposition;
          use (colimOfArrowsIn (diagram_pointwise (mapdiagram (pr1_category _) _) _) _)|];
        cbn; symmetry; etrans;
        [use (colimOfArrowsIn _ _ (ColimCocone_L_R _ _ _ _ (colimit_module_signature_diagram (mapdiagram strength_to_module_signature_functor d) _)))|];
        cbn; now rewrite assoc
      ).
    - intros; etrans.
      { refine (maponpaths _ _); use transportf_total2_paths_f. }
      etrans.
      { use (transportf_total2_paths_f (λ x, x --> _)). }
      cbn; use colimArrowUnique; intro u; unfold ColimFunctor_mor; cbn.
      use (colimOfArrowsIn _ _ (colims_V (diagram_pointwise (mapdiagram (pr1_category _) _) _))).
  Qed.

  Proposition signature_with_strength_to_module_signatures_limits (g : graph)
    (lims_V : Lims_of_shape g V)
    (d : diagram g (pointedtensorialstrength_cat Mon_V_swapped))
    : strength_to_module_signature_functor (limit_signature_with_strength _ lims_V d)
    = limit_module_signature (mapdiagram strength_to_module_signature_functor d) lims_V.
  Proof.
    use module_signature_equality.
    - intro R; use total2_paths_f.
      + use idpath. 
      + abstract (
          use subtypePath;
          [use isaprop_module_laws|];
          cbn;
          unfold limit_sig_strength_data, LimFunctor_mor, lim_module_subst;
          use limArrowUnique';
          intro u;
          etrans;
          [rewrite <- assoc; apply cancel_precomposition; use limOfArrowsOut|];
          rewrite assoc; etrans;
          [apply cancel_postcomposition; use limArrowCommutes|];
          symmetry; etrans;
          [use limArrowCommutes|];
          cbn; now rewrite assoc
        ).
    - intros; etrans.
      { refine (maponpaths _ _); use transportf_total2_paths_f. }
      etrans.
      { use (transportf_total2_paths_f (λ x, x --> _)). }
      cbn; use limArrowUnique; intro u; unfold ColimFunctor_mor; cbn.
      use (limArrowCommutes (lims_V (diagram_pointwise (mapdiagram (pr1_category _) d) _))).
  Qed.

  (** 4. Models are Sigma monoids *)
  Section ModelsAreSigmaMonoids.
    Context {H : V ⟶ V}.
    Context (θ : pointedtensorialstrength Mon_V_swapped H).

    Definition sigma_monoid_to_model
      (M : SigmaMonoid θ)
      : models_of_module_signatures_cat (strength_to_module_signature θ).
    Proof.
      use tpair; [|use tpair].
      - use monoid_swapped_to_monoid_mon; exact (SigmaMonoid_to_monoid θ M).
        (* SigmaMonoid_to_monoid gives an element of MON Mon_V_swapped and not MON Mon_V *)
      - exact (SigmaMonoid_τ θ M).
      - exact (!SigmaMonoid_is_compatible θ M).
    Defined.

    Definition model_to_sigma_monoid
      (M : models_of_module_signatures_cat (strength_to_module_signature θ))
      : SigmaMonoid θ.
    Proof.
      induction M as [[M M_mon] [τ hyp]].
      use (_ ,, (_ ,, _) ,, _); cbn.
      - exact M.
      - exact τ.
      - exact (monoid_to_monoid_swapped_monoid _ M_mon).
      - exact (!hyp).
    Defined.

    Definition sigma_monoid_to_model_functor_data
      : functor_data (SigmaMonoid θ) (models_of_module_signatures_cat (strength_to_module_signature θ)).
    Proof.
      exists sigma_monoid_to_model.
      intros M M' f.
      use ((_ ,, _ ,, _) ,, _); cbn.
      - exact (pr1 f).
      - abstract (
            unfold is_monoid_mor_mult; cbn; rewrite <- (monoidal_swapped_whiskering Mon_V); use (pr1 (pr212 f))
          ).
      - exact (pr2 (pr212 f)).
      - exact (pr112 f).
    Defined.

    Lemma sigma_monoid_to_model_functor_laws
      : is_functor sigma_monoid_to_model_functor_data.
    Proof.
      split.
      - intro.
        use subtypePath.
        { intro; use homset_property. }
        apply MON_mor_eq; easy.
      - intros ? ? ? ? ?.
        use subtypePath.
        { intro; use homset_property. }
        apply MON_mor_eq; easy.
    Qed.

    Definition sigma_monoid_to_model_functor
      : SigmaMonoid θ ⟶ models_of_module_signatures_cat (strength_to_module_signature θ)
      := make_functor _ sigma_monoid_to_model_functor_laws.

    Definition model_to_sigma_monoid_functor_data
      : functor_data (models_of_module_signatures_cat (strength_to_module_signature θ)) (SigmaMonoid θ).
    Proof.
      exists model_to_sigma_monoid.
      intros M M' f.
      use (_ ,, (_  ,, _ ,, _) ,, tt); cbn.
      - exact (pr11 f).
      - exact (pr2 f).
      - abstract (unfold is_monoid_mor_mult; rewrite (monoidal_swapped_whiskering Mon_V); exact (pr121 f)).
      - exact (pr221 f).
    Defined.

    Lemma model_to_sigma_monoid_functor_laws
      : is_functor model_to_sigma_monoid_functor_data.
    Proof.
      split.
      - intro.
        apply SigmaMonoid_mor_eq; easy.
      - intros ? ? ? ? ?.
        apply SigmaMonoid_mor_eq; easy.
    Qed.

    Definition model_to_sigma_monoid_functor
      : models_of_module_signatures_cat (strength_to_module_signature θ) ⟶ SigmaMonoid θ
      := make_functor _ model_to_sigma_monoid_functor_laws.

    Lemma sigma_monoid_to_model_functor_fully_faithful
      : fully_faithful sigma_monoid_to_model_functor.
    Proof.
      intros M M'.
      use (weqproperty (weq_iso (#sigma_monoid_to_model_functor) _ _ _)).
      - intro F.
        exists (pr11 F).
        use ((_ ,, _ ,, _) ,, tt); cbn.
        + use (pr2 F).
        + abstract (
            etrans; [| use (pr121 F)];
            use cancel_postcomposition;
            use monoidal_swapped_whiskering
          ).
        + abstract (use (pr221 F)).
      - intro f; cbn.
        use subtypePath.
        { intro; do 2 try use isapropdirprod.
          + use homset_property.
          + use isaprop_is_monoid_mor.
          + use isapropunit. }
        reflexivity.
      - intro f; cbn.
        use subtypePath.
        { intro; use homset_property. }
        use subtypePath.
        { intro; use isaprop_is_monoid_mor. }
        reflexivity.
    Qed.

    Lemma sigma_monoid_to_model_functor_isweq
      : isweq sigma_monoid_to_model_functor.
    Proof.
      use (weqproperty (weq_iso _ _ _ _)).
      - intro M.
        use (_ ,, (_ ,, _) ,, _); cbn.
        + exact (pr11 M).
        + exact (pr12 M).
        + use monoid_to_monoid_swapped_monoid.
          exact (pr21 M).
        + exact (!pr22 M).
      - intro M; cbn.
        use pair_path_in2.
        use subtypePath.
        { intro; use homset_property. }
        use pair_path_in2.
        use pair_path_in2.
        use proofirrelevance.
        use isaprop_monoid_laws.
      - intro M; cbn.
        use total2_paths2_f.
        { use total2_paths_f; [reflexivity|].
          use total2_paths_f; [reflexivity|].
          use proofirrelevance.
          use isaprop_monoid_laws. }
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        rewrite transportf_total2.
        use (transportf_total2_paths_f (λ x, H x --> x)).
    Qed.

    Definition iso_models_sigma_monoids
      : catiso (SigmaMonoid θ) (models_of_module_signatures_cat (strength_to_module_signature θ)).
    Proof.
      exists sigma_monoid_to_model_functor.
      split.
      - exact sigma_monoid_to_model_functor_fully_faithful.
      - exact sigma_monoid_to_model_functor_isweq.
    Defined.
  End ModelsAreSigmaMonoids.
End StrengthToModuleSignature.


(** 5. Instance where the functor is not essentially surjective *)

Section StrengthToModuleSignatureNotEssentiallySurjective.
  Let V : category := SET.
  Let Mon_V : monoidal V := SET_cartesian_monoidal.

  Let V_Mon : monoidal_cat := V ,, Mon_V.

  Local Definition two : V := (bool ,, isasetbool).

  Local Definition monoid_plus_monoid : monoid Mon_V two.
  Proof.
    use make_monoid; cbn.
    - intros h; induction h as [a b]; induction a, b.
      + exact false.
      + exact true.
      + exact true.
      + exact false.
    - intro; exact false.
    - abstract (use funextsec; intros (? , a); induction a; reflexivity).
    - abstract (use funextsec; intros (a , ?); induction a; reflexivity).
    - abstract (use funextsec; intros ((a, b), c); induction a, b, c; reflexivity).
  Defined.

  Local Definition monoid_plus : MON V_Mon := _ ,, monoid_plus_monoid.

  Local Definition monoid_times_monoid : monoid Mon_V two.
  Proof.
    use make_monoid; cbn.
    - intros h; induction h as [a b]; induction a, b.
      + exact true.
      + exact false.
      + exact false.
      + exact false.
    - intro; exact true.
    - abstract (use funextsec; intros (? , a); induction a; reflexivity).
    - abstract (use funextsec; intros (a , ?); induction a; reflexivity).
    - abstract (use funextsec; intros ((a, b), c); induction a, b, c; reflexivity).
  Defined.

  Local Definition monoid_times : MON V_Mon := _ ,, monoid_times_monoid.

  Local Definition signature_data
    : section_disp_data (@total_category_of_modules_disp_cat V_Mon).
  Proof.
    use tpair.
    - intro X; use tpair; cbn.
      + exists (monoid_times --> X).
        abstract (
          use isaset_total2;
          [use isaset_set_fun_space
          |intro; use isasetaprop; use isaprop_is_monoid_mor]
        ).
      + exists pr1; abstract (do 2 split).
    - intros X Y f; cbn; use tpair.
      + intro u;
        change (MON V_Mon ⟦ monoid_times, X⟧) in u.
        use (u · f).
      + reflexivity.
  Defined.

  Local Lemma signature_law
    : section_disp_axioms signature_data.
  Proof.
    split.
    - intro X; cbn.
      use subtypePath.
      { intro; use isaprop_is_module_mor. }
      cbn; use funextsec; intros [x y].
      use subtypePath.
      { intro; use isaprop_is_monoid_mor. }
      reflexivity.
    - intros X Y Z f f'; cbn.
      use subtypePath.
      { intro; use isaprop_is_module_mor. }
      cbn; use funextsec; intros [x y].
      use subtypePath.
      { intro; use isaprop_is_monoid_mor. }
      reflexivity.
  Qed.


  Local Definition signature : @module_signature_cat V_Mon.
  Proof.
    exists signature_data.
    exact signature_law.
  Defined.

  Section IfItWasIso.
    Context (hyp : ∑ (Hθ : pointedtensorialstrength_cat (Mon_V_swapped Mon_V)),
       z_iso (strength_to_module_signature_functor Mon_V Hθ) signature).

    Let H : V ⟶ V := pr11 hyp.
    Let Hθ := pr1 hyp.
    Let hyp_iso : z_iso (strength_to_module_signature_functor Mon_V Hθ) signature
      := pr2 hyp.

    Local Lemma monoid_times_iso 
      : z_iso (strength_to_module_signature_functor Mon_V Hθ monoid_times) (signature monoid_times).
    Proof.
      now use module_signature_iso_pointwise.
    Defined.

    Local Lemma monoid_plus_iso 
      : z_iso (strength_to_module_signature_functor Mon_V Hθ monoid_plus) (signature monoid_plus).
    Proof.
      now use module_signature_iso_pointwise.
    Defined.
     
    Let A_Set : SET := pr1 (signature monoid_times).
    Let B_Set : SET := pr1 (signature monoid_plus).

    Let A : UU := pr1 A_Set.
    Let B : UU := pr1 B_Set.

    Opaque A_Set B_Set.

    Local Lemma signature_image_iso
      : z_iso A_Set B_Set.
    Proof.
      use z_iso_comp.
      - use (H two).
      - use z_iso_inv.
        exact (functor_on_z_iso (forgetful _ _) monoid_times_iso).
      - exact (functor_on_z_iso (forgetful _ _) monoid_plus_iso).
    Defined.

    Local Lemma equivAB : A ≃ B.
    Proof.
      use hset_z_iso_equiv.
      use signature_image_iso.
    Defined.

    Local Definition f00 := λ _: bool, false.
    Local Definition f11 := λ _: bool, true.
    Local Definition f01 := λ b: bool, bool_rect (λ _, bool) false true b.
    Local Definition f10 := λ b: bool, bool_rect (λ _, bool) true false b.

    Local Lemma boolToBool_eq (f : bool -> bool)
      : (f = f00) ⨿ (f = f01) ⨿ (f = f10) ⨿ (f = f11).
    Proof.
      assert (∏ x, (f x = true) ⨿ (f x = false)) as f_eq.
      { intro x; induction (f x); [left|right]; reflexivity. }
      induction (f_eq true), (f_eq false).
      - do 0 left; try right; use funextsec; intro u; induction u; assumption.
      - do 1 left; try right; use funextsec; intro u; induction u; assumption.
      - do 2 left; try right; use funextsec; intro u; induction u; assumption.
      - do 3 left; try right; use funextsec; intro u; induction u; assumption.
    Defined.

    Local Lemma times_to_times
      (f : bool -> bool)
      (f_hyp : is_monoid_mor Mon_V monoid_times_monoid monoid_times_monoid f)
      : (f = f11) ⨿ (f = f10).
    Proof.
      induction (boolToBool_eq f) as [[[h | h] | h] | h]; rewrite h in f_hyp.
      3: { right; assumption. }
      3: { left; assumption. }
      all: use fromempty; use nopathsfalsetotrue;
           exact (maponpaths (λ u, u tt) (pr2 f_hyp)).
    Defined.

    Local Lemma times_to_plus
      (f : bool -> bool)
      (f_hyp : is_monoid_mor Mon_V monoid_times_monoid monoid_plus_monoid f)
      : f = f00.
    Proof.
      induction (boolToBool_eq f) as [[[h | h] | h] | h]; rewrite h in f_hyp.
      - assumption. 
      - use fromempty; use nopathsfalsetotrue.
        exact (maponpaths (λ u, u (false ,, false)) (pr1 f_hyp)).
      - use fromempty; use nopathstruetofalse.
        exact (maponpaths (λ u, u (true ,, false)) (pr1 f_hyp)).
      - use fromempty; use nopathsfalsetotrue.
        exact (maponpaths (λ u, u (true ,, false)) (pr1 f_hyp)).
    Defined.

    Local Lemma equiv2A : bool ≃ A.
    Proof.
      use weq_iso.
      - intro b; induction b; cbn.
        + exists (λ x, true); abstract (do 2 split).
        + exists (λ x, x); abstract (do 2 split).
      - intros (f , f_hyp).
        apply (coprodtobool (times_to_times _ f_hyp)).
      - intro b; induction b; reflexivity.
      - intros (f , f_hyp).
        use subtypePath.
        { intro; use isaprop_is_monoid_mor. }
        induction (times_to_times f f_hyp) as [h | h]; cbn; rewrite h;
        use funextsec; intro b; now induction b.
    Defined.

    Local Lemma equivB1 : B ≃ unit.
    Proof.
      use weq_iso.
      - exact tounit.
      - intro u; clear u; exists (λ _, false); split; split.
      - intros (f , f_hyp); cbn.
        use subtypePath.
        { intro; use isaprop_is_monoid_mor. }
        cbn; now rewrite (times_to_plus f f_hyp).
      - intro y; now induction y.
    Defined.


    Local Lemma equiv21 : bool ≃ unit.
    Proof.
      refine (weqcomp equiv2A (weqcomp equivAB equivB1)).
    Defined.

    Local Lemma contradiction 
      : empty.
    Proof.
      assert (iscontr bool) by (use iscontrifweqtounit; use equiv21).
      induction X as [b p].
      specialize (p (negb b)).
      induction b; now use nopathsfalsetotrue.
    Qed.

  End IfItWasIso.

  Theorem strength_to_module_not_essentially_surjective
    : ¬ essentially_surjective (strength_to_module_signature_functor Mon_V).
  Proof.
    intro; eapply factor_through_squash.
    - use isapropempty.
    - use contradiction.
    -use (X signature).
  Qed.
End StrengthToModuleSignatureNotEssentiallySurjective.
