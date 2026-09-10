(***************************************************************************

 (Right) Module Signatures

 In this file, we define signatures as sections of the forgetful functor from
 the total category of right modules to the category of monoids.

 They form a category "module_signature_cat".

 Contents
 1. Definitions
 2. Two examples of module signatures
 3. Evaluation functor (for some fixed monoid R)

 ***************************************************************************)

Require Import UniMath.Tactics.EnsureStructuredProofs.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope mor_disp_scope.

Section ModuleSignatures.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  (**
     1. Definitions
   *)

  (* We use displayed sections, as total_category_of_modules is a displayed category *)

  Definition module_signature_data
    := @section_disp_data (MON C) total_category_of_modules_disp_cat.

  Definition module_signature_cat : category
    := @section_disp_cat (MON C) total_category_of_modules_disp_cat.

  Definition module_signature_disp_on_objects (Σ : module_signature_data) (R : MON C)
    : MOD (pr1 R) (pr2 R) := pr1 Σ R.

  Definition module_signature_disp_cat_to_data (Σ : module_signature_cat)
    : module_signature_data := pr1 Σ.

  Coercion module_signature_disp_on_objects : module_signature_data >-> Funclass.
  Coercion module_signature_disp_cat_to_data : ob >-> module_signature_data.

  Definition module_signature_axioms (Σ : module_signature_data)
    := section_disp_axioms Σ.

  Lemma module_signature_equality (Σ Σ' : module_signature_cat)
    (equality_on_objects : ∏ A, Σ A = Σ' A)
    (equality_on_morphisms : ∏ (A A' : MON C) (f : A --> A'),
      transportf
        (λ ΣA : MOD (pr1 A) (pr2 A), C ⟦ pr1 ΣA, pr1 (Σ' A') ⟧)
        (equality_on_objects A)
        (transportf
           (λ ΣA' : MOD (pr1 A') (pr2 A'), C ⟦ pr1 (Σ A), pr1 ΣA' ⟧)
           (equality_on_objects A') (pr1 (section_disp_on_morphisms (pr1 Σ) f))) =
      pr1 (section_disp_on_morphisms (pr1 Σ') f))
    : Σ = Σ'.
  Proof.
    use section_disp_equality.
    - intros; use homset_property.
    - intro; use equality_on_objects.
    - intros.
      apply MOD_mor_eq.
      cbn.
      rewrite transportf_total2.
      rewrite transportf_total2.
      use equality_on_morphisms.
  Qed.

  (**
     2. Two examples of module signatures
   *)

  Definition trivial_signature_data : module_signature_data.
  Proof.
    use tpair; cbn.
    - intro; use trivial_module.
    - intros R R' [f H_f].
      exists f.
      abstract (
        unfold is_module_mor; cbn;
        rewrite assoc; use (pr1 H_f)
      ).
  Defined.

  Lemma trivial_signature_axioms
    : module_signature_axioms trivial_signature_data.
  Proof.
    split; intros; apply MOD_mor_eq; easy.
  Qed.

  Definition trivial_signature : module_signature_cat
    := trivial_signature_data ,, trivial_signature_axioms.

  Lemma product_module_signature_lemma (Σ : module_signature_cat) (D : C)
    (R R' : MON C) (f : R --> R') (Σf := section_disp_on_morphisms (pr1 Σ) f)
    : is_module_mor _ _
        (pr2 (product_module _ _ _ _ (pr2 (Σ R))))
        (pullback_functor_funct _ (pr2 (product_module _ _ _ D (pr2 (Σ R')))) _ (pr2 f))
        (D ⊗l pr1 Σf).
  Proof.
    unfold is_module_mor; cbn. unfold product_module_subst. do 2 rewrite assoc.
    symmetry; etrans; etrans.
    - rewrite <- assoc; use maponpaths; [shelve|symmetry].
      use (bifunctor_leftcomp C).
    - do 2 (use maponpaths; [shelve|]);
      use (!pr2 Σf).
    - rewrite (bifunctor_leftcomp C), assoc, (monoidal_associatornatleftright C), <- assoc.
      use maponpaths; [shelve|cbn].
      now rewrite (bifunctor_leftcomp C), assoc, (monoidal_associatornatleft C).
    - now do 2 rewrite assoc.
  Qed.

  Definition product_signature_data (Σ : module_signature_cat) (D : C)
    : module_signature_data.
  Proof.
    use tpair; cbn.
    - intro R; use (product_module _ _ _ D (pr2 (Σ R))).
    - intros R R' f; pose (section_disp_on_morphisms (pr1 Σ) f) as Σf.
      exists (D ⊗l pr1 Σf); use product_module_signature_lemma.
  Defined.

  Lemma product_signature_axioms (Σ : module_signature_cat) (D : C)
    : module_signature_axioms (product_signature_data Σ D).
  Proof.
    split.
    - intro R. apply MOD_mor_eq.
      cbn; etrans.
      + do 2 (use maponpaths; [shelve|]); use (pr12 Σ R).
      + cbn; now rewrite tensor_mor_left, tensor_id_id.
    - intros R R' R'' f g. apply MOD_mor_eq.
      cbn; etrans.
      + do 2 (use maponpaths; [shelve|]); use (pr22 Σ R).
      + use (bifunctor_leftcomp C).
  Qed.

  Definition product_signature (Σ : module_signature_cat) (D : C)
    : module_signature_cat
    := product_signature_data Σ D,, product_signature_axioms Σ D.

  (**
     3. Evaluation functor (for some fixed monoid R)
   *)

  Section FixAMonoid.
    Context (R : MON C).
    Let MOD_R := MOD (pr1 R) (pr2 R).


    Definition signature_evaluation_data
      : functor_data module_signature_cat MOD_R.
    Proof.
      use make_functor_data.
      - intro Σ; exact (Σ R).
      - intros Σ Σ' [f _]; induction (f R) as [fR H].
        exists fR.
        abstract (
          cbn in fR, H |- *;
          unfold is_module_mor, pullback_functor_funct in *;
          cbn in fR, H |- *;
          etrans;
          [|use H];
          now rewrite assoc, tensor_mor_left, tensor_id_id, id_right
        ).
    Defined.

    Lemma signature_evaluation_is_functor
      : is_functor signature_evaluation_data.
    Proof.
      split.
      - intro Σ. apply MOD_mor_eq.
        easy.
      - intros Σ Σ' Σ'' f g; apply MOD_mor_eq; cbn; unfold mor_disp; cbn.
        now rewrite transportf_total2, transportf_const.
    Qed.


    Definition signature_evaluation : module_signature_cat ⟶ MOD_R
      := make_functor signature_evaluation_data signature_evaluation_is_functor.
  End FixAMonoid.


  Section Colimits.
    Context {g : graph}.
    Context (d : diagram g module_signature_cat).
    Context (colims_g : Colims_of_shape g C).
    Context (HR : ∏ R : MON C, preserves_colimits_of_shape (rightwhiskering_functor C (pr1 R)) g).

    Let Σ v : module_signature_data := dob d v.

    Definition colimit_module_signature_diagram (R : MON C) 
      : diagram g (MOD (pr1 R) (pr2 R))
      := mapdiagram (signature_evaluation R) d.

    Definition colimit_module_signature_colimcocone (R : MON C)
      : ColimCocone (colimit_module_signature_diagram R)
      := MOD_inherits_colimits _ _ _ colims_g (HR R) (colimit_module_signature_diagram R).

    Definition colimit_module_signature_objects (R : MON C)
      : MOD (pr1 R) (pr2 R)
      := colim (colimit_module_signature_colimcocone R).

    Let L R := colimit_module_signature_objects R.

    Opaque MOD_inherits_colimits.

    Definition colimit_module_signature_morphisms_cocone_data
      (R R' : MON C) (f : R --> R') (v : vertex g)
      : MOD (pr1 R) (pr2 R) ⟦ 
          dob (colimit_module_signature_diagram R) v,
          pullback_functor' R R' f (L R') ⟧.
    Proof.
      refine (_ · _).
      - exact (section_disp_on_morphisms (Σ v) f).
      - apply (# (pullback_functor' _ _ f)).
        exact (colimIn (colimit_module_signature_colimcocone R') v).
    Defined.

    Lemma colimit_module_signature_morphisms_cocone_law
      (R R' : MON C) (f : R --> R') 
      : forms_cocone _ (colimit_module_signature_morphisms_cocone_data _ _ f).
    Proof.
      intros u v e; cbn.
      use subtypePath.
      { intro; use isaprop_is_module_mor. }
      cbn; rewrite assoc; symmetry; etrans.
      { apply cancel_precomposition.
        use (maponpaths pr1 (!colimInCommutes (colimit_module_signature_colimcocone R') _ _ e)). }
      cbn; rewrite assoc; use cancel_postcomposition.
      etrans.
      2: { exact (maponpaths pr1 (pr2 (dmor d e) _ _ f)). }  
      unfold mor_disp; simpl.
      rewrite transportf_total2; simpl.
      now rewrite transportf_const.
    Qed.

    Definition colimit_module_signature_morphisms_cocone
      (R R' : MON C) (f : R --> R')
      : cocone (colimit_module_signature_diagram R) (pullback_functor' R R' f (L R')).
    Proof.
      use make_cocone.
      - apply colimit_module_signature_morphisms_cocone_data.
      - apply colimit_module_signature_morphisms_cocone_law.
    Defined.

    Definition colimit_module_signature_morphisms
      (R R' : MON C) (f : R --> R')
      : total_category_of_modules⟦(R ,, L R) , (R' ,, L R')⟧.
    Proof.
      exists f.
      use (colimArrow _ (pullback_functor' _ _ _ _)).
      use colimit_module_signature_morphisms_cocone.
    Defined.

    Definition colimit_module_signature_data : module_signature_data.
    Proof.
      use tpair.
      - exact colimit_module_signature_objects.
      - intros R R' f; apply colimit_module_signature_morphisms.
    Defined.

    Lemma colimit_module_signature_axioms
      : section_disp_axioms colimit_module_signature_data.
    Proof.
      split.
      - intro R; cbn.
        symmetry.
        use (colimArrowUnique _ _ (colimit_module_signature_morphisms_cocone _ _ (identity _))).
        intro u; cbn; use subtypePath.
        { intro. use isaprop_is_module_mor. }
        cbn; symmetry.
        rewrite id_right, <- id_left.
        use cancel_postcomposition.
        use (maponpaths pr1 (section_disp_id (dob d u) _)).
      - intros R R' R'' f f'; cbn.
        symmetry.
        use (colimArrowUnique _ _ (colimit_module_signature_morphisms_cocone _ _ (f · f'))).
        intro u; cbn; use subtypePath.
        { intro. use isaprop_is_module_mor. }
        cbn; rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply (maponpaths pr1 (colimArrowCommutes (colimit_module_signature_colimcocone R)
            _ (colimit_module_signature_morphisms_cocone _ _ _) _)). }
        cbn; etrans.
        { rewrite <- assoc; apply cancel_precomposition.
          apply (maponpaths pr1 (colimArrowCommutes (colimit_module_signature_colimcocone R')
            _ (colimit_module_signature_morphisms_cocone _ _ _) _)). }
        cbn; rewrite assoc; use cancel_postcomposition.
        use (maponpaths pr1 (!section_disp_comp (dob d u) _ _ _ _ _)).
    Qed.

    Definition colimit_module_signature : module_signature_cat
      := colimit_module_signature_data ,,
         colimit_module_signature_axioms.

    Transparent MOD_inherits_colimits.

    Definition colimit_module_signature_cocone
      : cocone d colimit_module_signature.
    Proof.
      use make_cocone.
      - intro v; use tpair.
        + intro R; simpl.
          exists (pr1 (colimIn (colimit_module_signature_colimcocone R) v)).
          abstract (
            unfold is_module_mor; cbn;
            rewrite tensor_mor_left, tensor_id_id, id_left;
            cbn; unfold colim_module_subst; cbn;
            use (colimOfArrowsIn _ _ (ColimCocone_L_R _ _ _ _ (colimit_module_signature_diagram R)))
          ).
        + abstract (
            intros R R' f; cbn;
            use subtypePath; [intro; use isaprop_is_module_mor|];
            unfold mor_disp; cbn;
            rewrite transportf_total2; cbn;
            rewrite transportf_const; cbn;
            symmetry; use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R))))
          ).
      - abstract (
          intros u v e; cbn;
          use subtypePath;
          [intro; use isaprop_section_nat_trans_disp_axioms|];
          cbn; use funextsec; intro R;
          unfold mor_disp; cbn;
          use subtypePath;
          [intro; use isaprop_is_module_mor|];
          rewrite transportf_total2; cbn;
          rewrite transportf_const; cbn;
          use (maponpaths pr1 (colimInCommutes (colimit_module_signature_colimcocone R) _ _ e))
        ).
    Defined.

    Section FixACocone.
      Context (Σ' : module_signature_cat) (cc : cocone d Σ').

      Let cc' R := mapcocone (signature_evaluation R) _ cc.

      Lemma colimit_module_signature_arrow_is_module_mor (R : MON C)
        : is_module_mor _ _ 
          (colim_module _ _ colims_g (HR _) _)
          (pullback_functor_funct _ (pr2 (Σ' R)) _ (id_disp (pr2 R))) 
          (pr1 (colimArrow (colimit_module_signature_colimcocone R) _ (cc' R))).
      Proof.
        unfold is_module_mor; cbn.
        rewrite tensor_mor_left, tensor_id_id, id_left.
        use (colimArrowUnique' (ColimCocone_L_R _ _ _ (HR R) (colimit_module_signature_diagram R))).
        intro; do 2 rewrite assoc; etrans.
        { apply cancel_postcomposition.
          cbn; rewrite <- (bifunctor_rightcomp C).
          apply maponpaths.
          use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R)))). }
        unfold colim_module_subst; cbn.
        symmetry; etrans.
        { apply cancel_postcomposition.
          use (colimOfArrowsIn _ _ (ColimCocone_L_R _ _ _ _ (colimit_module_signature_diagram R))). }
        cbn; etrans.
        { rewrite <- assoc; apply cancel_precomposition.
          use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R)))). }
        cbn.
        etrans.
        { exact (!pr2 (pr1 (coconeIn cc u) R)). }
        cbn.
        now rewrite tensor_mor_left, tensor_id_id, id_left.
      Qed.

      Definition colimit_module_signature_arrow_data
        : section_nat_trans_disp_data colimit_module_signature Σ'.
      Proof.
        intro R; eexists; use colimit_module_signature_arrow_is_module_mor.
      Defined.

      Lemma colimit_module_signature_arrow_nat
        : section_nat_trans_disp_axioms colimit_module_signature_arrow_data.
      Proof.
        intros R R' f; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        rewrite transportf_const; cbn.
        use colimArrowUnique'; intro; do 2 rewrite assoc.
        etrans.
        { apply cancel_postcomposition; use colimArrowCommutes. }
        cbn; etrans.
        { rewrite <- assoc; apply cancel_precomposition.
          use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R')))). }
        cbn; symmetry; etrans.
        { apply cancel_postcomposition.
          use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R)))). }
        cbn.
        etrans.
        { exact (!maponpaths pr1 (pr2 (coconeIn cc u) _ _ f )). }
        cbn.
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        now rewrite transportf_const.
      Qed.

      Definition colimit_module_signature_arrow 
        : module_signature_cat ⟦ colimit_module_signature, Σ' ⟧.
      Proof.
        exists colimit_module_signature_arrow_data.
        use colimit_module_signature_arrow_nat.
      Defined.

      Lemma colimit_module_signature_arrow_is_cocone_mor
        : is_cocone_mor colimit_module_signature_cocone cc colimit_module_signature_arrow.
      Proof.
        intro; cbn.
        use subtypePath.
        { intro; use isaprop_section_nat_trans_disp_axioms. }
        cbn; use funextsec; intro R.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        rewrite transportf_const; cbn.
        use (colimArrowCommutes (colims_g (mapdiagram (forgetful _ _) (colimit_module_signature_diagram R)))).
      Qed.

      Context (pair : ∑ (γ : module_signature_cat ⟦ colimit_module_signature, Σ' ⟧),
        is_cocone_mor colimit_module_signature_cocone cc γ).

      Let γ : module_signature_cat ⟦ colimit_module_signature, Σ' ⟧ := pr1 pair.
      Let γ_hyp : is_cocone_mor colimit_module_signature_cocone cc γ := pr2 pair.

      Lemma colimit_module_signature_arrow_unique
        : γ = colimit_module_signature_arrow.
      Proof.
        use subtypePath.
        { intro; use isaprop_section_nat_trans_disp_axioms. }
        use funextsec; intro R; cbn.
        unfold colimit_module_signature_arrow_data; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        cbn.
        use colimArrowUnique; intro u; cbn.
        rewrite <- γ_hyp; cbn.
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        now rewrite transportf_const.
      Qed.

      Lemma colimit_module_signature_arrow_unique_pair
        : pair = colimit_module_signature_arrow ,, colimit_module_signature_arrow_is_cocone_mor.
      Proof.
        use subtypePath.
        - intro; use isaprop_is_cocone_mor.
        - use colimit_module_signature_arrow_unique.
      Qed.
    End FixACocone.

    Definition colimit_module_signature_ColimCocone : ColimCocone d.
    Proof.
      use make_ColimCocone.
      - exact colimit_module_signature.
      - exact colimit_module_signature_cocone.
      - intros ? ?; eexists; use colimit_module_signature_arrow_unique_pair.
    Defined.
  End Colimits.

  Theorem module_signature_inherits_colimits (g : graph) (_ : Colims_of_shape g C)
    (_ : ∏ R : MON C, preserves_colimits_of_shape (rightwhiskering_functor C (pr1 R)) g)
    : Colims_of_shape g module_signature_cat.
  Proof.
    intro; now use colimit_module_signature_ColimCocone.
  Defined.

  Section Limits.
    Context {g : graph}.
    Context (d : diagram g module_signature_cat).
    Context (lims_g : Lims_of_shape g C).

    Let Σ v : module_signature_data := dob d v.

    Definition limit_module_signature_diagram (R : MON C) 
      : diagram g (MOD (pr1 R) (pr2 R))
      := mapdiagram (signature_evaluation R) d.

    Definition limit_module_signature_limcone (R : MON C)
      : LimCone (limit_module_signature_diagram R)
      := MOD_inherits_limits _ _ _ lims_g (limit_module_signature_diagram R).

    Definition limit_module_signature_objects (R : MON C)
      : MOD (pr1 R) (pr2 R)
      := lim (limit_module_signature_limcone R).

    Let L R := limit_module_signature_objects R.

    Let diagram_in_C R := mapdiagram (forgetful (pr1 R) (pr2 R)) (limit_module_signature_diagram R).

    Lemma limit_module_signature_morphisms_data 
      (R R' : MON C) (f : R --> R')
      : C ⟦ lim (lims_g (diagram_in_C R)), lim (lims_g (diagram_in_C R'))⟧.
    Proof.
      use limOfArrows; cbn.
      - intro u; exact (pr1 (section_disp_on_morphisms (Σ u) f)).
      - abstract (
          intros u v e; cbn;
          etrans; [|use (maponpaths pr1 (pr2 (dmor d e) _ _ f))];
          unfold mor_disp; cbn;
          rewrite transportf_total2; cbn;
          now rewrite transportf_const
        ).
    Defined.

    Lemma limit_module_signature_morphisms_is_module_mor
      (R R' : MON C) (f : R --> R')
      : is_module_mor _ _
          (lim_module _ _ lims_g _)
          (pullback_functor_funct _ (lim_module _ _ lims_g _) _ (pr2 f))
          (limit_module_signature_morphisms_data R R' f).
    Proof.
      unfold is_module_mor; cbn.
      transparent assert (cc : (cone (diagram_in_C R') (lim (lims_g (diagram_in_C R)) ⊗ pr1 R))).
      { use make_cone.
        - intro u; cbn.
          refine (_ · _ · _); swap 1 3.
          + exact (pr1 (section_disp_on_morphisms (Σ u) f)).
          + exact (limOut (lims_g (diagram_in_C R)) u).
          + exact (pr12 (limit_module_signature_objects R)).
        - abstract  (
            intros u v e; cbn;
            do 3 rewrite <- assoc; apply cancel_precomposition;
            rewrite <- (limOutCommutes _ _ _ e), <- assoc; apply cancel_precomposition;
            etrans; [| apply (maponpaths pr1 (pr2 (dmor d e) _ _ f))];
            unfold mor_disp; simpl;
            rewrite transportf_total2; cbn;
            now rewrite transportf_const
          ). }
      etrans; [|symmetry].
      - use (limArrowUnique _ _ cc).
        intro; unfold limit_module_signature_morphisms_data, lim_module_subst; cbn.
        rewrite assoc; etrans.
        { do 2 rewrite <- assoc.
          do 2 apply cancel_precomposition.
          use (limArrowCommutes (lims_g (diagram_in_C R'))). }
        cbn; do 2 rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          rewrite <- assoc.
          apply cancel_precomposition.
          symmetry; apply (bifunctor_equalwhiskers C). }
        unfold functoronmorphisms1; rewrite assoc.
        etrans.
        { do 2 apply cancel_postcomposition.
          rewrite <- (bifunctor_rightcomp C).
          apply maponpaths.
          use (limOfArrowsOut _ _ (lims_g (diagram_in_C R)) (lims_g (diagram_in_C R'))). }
        cbn. rewrite (bifunctor_rightcomp C).
        symmetry; etrans.
        { apply cancel_postcomposition; unfold lim_module_subst; cbn.
          use (limArrowCommutes (lims_g (diagram_in_C R))). }
        cbn.
        do 3 rewrite <- assoc; use cancel_precomposition.
        refine (!pr2 (section_disp_on_morphisms (Σ u) f)).
      - use (limArrowUnique _ _ cc).
        intro u; cbn.
        do 2 rewrite <- assoc; use cancel_precomposition.
        use (limOfArrowsOut _ _ (lims_g (diagram_in_C R)) (lims_g (diagram_in_C R'))).
    Qed.

    Definition limit_module_signature_morphisms
      (R R' : MON C) (f : R --> R')
      : total_category_of_modules⟦(R ,, L R) , (R' ,, L R')⟧.
    Proof.
      exists f; exists (limit_module_signature_morphisms_data _ _ f).
      apply limit_module_signature_morphisms_is_module_mor.
    Defined.

    Definition limit_module_signature_data : module_signature_data.
    Proof.
      use tpair.
      - exact limit_module_signature_objects.
      - intros R R' f; apply limit_module_signature_morphisms.
    Defined.

    Lemma limit_module_signature_axioms
      : section_disp_axioms limit_module_signature_data.
    Proof.
      split.
      - intro R; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        cbn; symmetry; use lim_endo_is_identity.
        intro u; cbn.
        unfold limit_module_signature_morphisms_data.
        etrans.
        { use (limOfArrowsOut _ _ (lims_g (diagram_in_C R)) (lims_g (diagram_in_C R))). }
        cbn.
        rewrite <- id_right; use cancel_precomposition.
        use (maponpaths pr1 (section_disp_id (dob d u) R)).
      - intros R R' R'' f f'; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        cbn; unfold limit_module_signature_morphisms_data, limOfArrows.
        symmetry; use limArrowUnique; cbn.
        intro u.
        etrans.
        { rewrite <- assoc; apply cancel_precomposition.
          use (limArrowCommutes (lims_g (diagram_in_C R''))). }
        cbn; rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          use (limArrowCommutes (lims_g (diagram_in_C R'))). }
        cbn.
        rewrite <- assoc; use cancel_precomposition.
        use (!maponpaths pr1 (section_disp_comp (dob d u) _ _ _ f f')).
    Qed.

    Definition limit_module_signature : module_signature_cat
      := limit_module_signature_data ,,
         limit_module_signature_axioms.

    Definition limit_module_signature_cone
      : cone d limit_module_signature.
    Proof.
      use make_cone.
      - intro v; use tpair.
        + intro R; simpl.
          exists (pr1 (limOut (limit_module_signature_limcone R) v)).
          abstract (
            unfold is_module_mor; cbn;
            rewrite tensor_mor_left, tensor_id_id, id_left;
            cbn; unfold lim_module_subst; cbn;
            symmetry; use (limArrowCommutes (lims_g (diagram_in_C R)))
          ).
        + abstract (
            intros R R' f; cbn;
            use subtypePath; [intro; use isaprop_is_module_mor|];
            unfold mor_disp; cbn;
            rewrite transportf_total2; cbn;
            rewrite transportf_const; cbn;
            use (limOfArrowsOut _ _ (lims_g (diagram_in_C R)) (lims_g (diagram_in_C R')))
          ).
      - abstract (
          intros u v e; cbn;
          use subtypePath;
          [intro; use isaprop_section_nat_trans_disp_axioms|];
          cbn; use funextsec; intro R;
          unfold mor_disp; cbn;
          use subtypePath;
          [intro; use isaprop_is_module_mor|];
          rewrite transportf_total2; cbn;
          rewrite transportf_const; cbn;
          use (maponpaths pr1 (limOutCommutes (limit_module_signature_limcone R) _ _ e))
        ).
    Defined.

    Section FixACone.
      Context (Σ' : module_signature_cat) (cc : cone d Σ').

      Let cc' R := mapcone (signature_evaluation R) _ cc.

      Lemma limit_module_signature_arrow_is_module_mor (R : MON C)
        : is_module_mor _ _ (pr2 (Σ' R))
            (pullback_functor_funct _ (lim_module _ _ lims_g _) _ (id_disp (pr2 R)))
            (pr1 (limArrow (limit_module_signature_limcone R) _ (cc' R))).
      Proof.
        unfold is_module_mor; cbn.
        rewrite tensor_mor_left, tensor_id_id, id_left.
        transparent assert (c : (cone (diagram_in_C R) (pr1 (Σ' R) ⊗ pr1 R))).
        {
          use make_cone.
          - intro v; exact (pr12 (Σ' R) · pr1 (pr1 (coneOut cc v) R)).
          - abstract (
              intros u v e; rewrite <- assoc; use cancel_precomposition;
              refine (_ @ maponpaths (λ x, pr1 (pr1 x R)) (coneOutCommutes cc _ _ e)); cbn;
              unfold mor_disp; cbn;
              rewrite transportf_total2; cbn; now rewrite transportf_const
            ).
        }

        etrans; [|symmetry]; use (limArrowUnique _ _ c); intro u; cbn.

        { unfold lim_module_subst; etrans; cbn.
          { rewrite <- assoc; apply cancel_precomposition.
            use (limArrowCommutes (lims_g (diagram_in_C R))). }
          cbn.
          rewrite assoc, <- (bifunctor_rightcomp C).
          etrans.
          { apply cancel_postcomposition; apply maponpaths.
            use (limArrowCommutes (lims_g (diagram_in_C R))). }
          cbn.
          refine (_ @ pr2 (pr1 (coneOut cc u) R)).
          cbn.
          now rewrite tensor_mor_left, tensor_id_id, id_left. }

        { rewrite <- assoc; apply cancel_precomposition.
          use (limArrowCommutes (lims_g (diagram_in_C R))). }
      Qed.

      Definition limit_module_signature_arrow_data
        : section_nat_trans_disp_data Σ' limit_module_signature .
      Proof.
        intro R; eexists; use limit_module_signature_arrow_is_module_mor.
      Defined.

      Lemma limit_module_signature_arrow_nat
        : section_nat_trans_disp_axioms limit_module_signature_arrow_data.
      Proof.
        intros R R' f; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        rewrite transportf_const; cbn.

        transparent assert (c : (cone (diagram_in_C R') (pr1 (Σ' R)))).
        { use make_cone.
          - intro v; exact (pr1 (section_disp_on_morphisms (pr1 Σ') f) · pr1 (pr1 (coneOut cc v) R')).
          - abstract (
              intros u v e; rewrite <- assoc; use cancel_precomposition; cbn;
              refine (_ @ maponpaths (λ x, pr1 (pr1 x R')) (coneOutCommutes cc _ _ e));
              cbn; unfold mor_disp; cbn;
              rewrite transportf_total2; cbn;
              now rewrite transportf_const
            ). }

        etrans.
        { use (limArrowUnique _ _ c); intro u; cbn.
          rewrite <- assoc; apply cancel_precomposition. 
          use (limArrowCommutes (lims_g (diagram_in_C R'))). }

        symmetry; use (limArrowUnique _ _ c); intro u; cbn.
        unfold limit_module_signature_morphisms_data.
        etrans.
        { rewrite <- assoc.
          apply cancel_precomposition.
          apply (limOfArrowsOut _ _ (lims_g (diagram_in_C R)) (lims_g (diagram_in_C R'))). }
        rewrite assoc; cbn; etrans.
        { apply cancel_postcomposition.
          apply (limArrowCommutes (lims_g (diagram_in_C R))). }
        refine (!maponpaths pr1 (pr2 (coneOut cc u) _ _ f) @ _); cbn.
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        now rewrite transportf_const.
      Qed.

      Definition limit_module_signature_arrow 
        : module_signature_cat ⟦ Σ', limit_module_signature ⟧.
      Proof.
        exists limit_module_signature_arrow_data.
        use limit_module_signature_arrow_nat.
      Defined.

      Lemma limit_module_signature_arrow_is_cone_mor
        : is_cone_mor cc limit_module_signature_cone limit_module_signature_arrow.
      Proof.
        intro; cbn.
        use subtypePath.
        { intro; use isaprop_section_nat_trans_disp_axioms. }
        cbn; use funextsec; intro R.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        rewrite transportf_const; cbn.
        use (limArrowCommutes (lims_g (mapdiagram (forgetful _ _) (limit_module_signature_diagram R)))).
      Qed.

      Context (pair : ∑ (γ : module_signature_cat ⟦ Σ', limit_module_signature ⟧),
        is_cone_mor cc limit_module_signature_cone γ).

      Let γ : module_signature_cat ⟦ Σ', limit_module_signature ⟧ := pr1 pair.
      Let γ_hyp : is_cone_mor cc limit_module_signature_cone γ := pr2 pair.

      Lemma limit_module_signature_arrow_unique
        : γ = limit_module_signature_arrow.
      Proof.
        use subtypePath.
        { intro; use isaprop_section_nat_trans_disp_axioms. }
        use funextsec; intro R; cbn.
        unfold limit_module_signature_arrow_data; cbn.
        use subtypePath.
        { intro; use isaprop_is_module_mor. }
        cbn.
        use limArrowUnique; intro u; cbn.
        rewrite <- γ_hyp; cbn.
        unfold mor_disp; cbn.
        rewrite transportf_total2; cbn.
        now rewrite transportf_const.
      Qed.

      Lemma limit_module_signature_arrow_unique_pair
        : pair = limit_module_signature_arrow ,, limit_module_signature_arrow_is_cone_mor.
      Proof.
        use subtypePath.
        - intro; use isaprop_is_cone_mor.
        - use limit_module_signature_arrow_unique.
      Qed.
    End FixACone.

    Definition limit_module_signature_LimCone : LimCone d.
    Proof.
      use make_LimCone.
      - exact limit_module_signature.
      - exact limit_module_signature_cone.
      - intros ? ?; eexists; use limit_module_signature_arrow_unique_pair.
    Defined.
  End Limits.

  Theorem module_signature_inherits_limits (g : graph) (_ : Lims_of_shape g C)
    : Lims_of_shape g module_signature_cat.
  Proof.
    intro; now use limit_module_signature_LimCone.
  Defined.

End ModuleSignatures.
