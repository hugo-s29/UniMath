(** In this file, we show how any monoid in the monoidal category of endofunctors is a monad  - here w.r.t. the
    elementary definition of that monoidal category

    the bicategorical variant is found in [MonadsAsMonoidsWhiskered]

    we also show the direction from monads to monoids, also showing
    that the category of monads in C is equivalent to the category
    of monoids in [C, C]

   Contents:
   1. Monads and monoids in [C, C] are isomorphic
   2. Monad modules and monoid modules are isomorphic
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.BicatOfCatsElementary.

Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.

Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Local Open Scope cat.


(** 1. Monads and monoids in [C, C] are isomorphic *)
Section FixACategory.

  Context {C : category}.

  Let EndC : monoidal_cat := monendocat_monoidal_cat C.

  Let EndC_swapped : monoidal_cat :=  _ ,, monoidal_swapped EndC.

  Let Monoid : category := category_of_monoids_in_monoidal_cat EndC.
  Let Monad : category := category_Monad C.

  Let Monoid_swapped : category := category_of_monoids_in_monoidal_cat EndC_swapped.

  Let Monoids_swapped : category := category_of_monoids_in_monoidal_cat EndC_swapped.

Section MonoidToMonad.

Section OnObjects.

  Context (M : Monoid).

  Let x := monoid_carrier _ M.
  Let η := monoid_unit _ M.
  Let μ := monoid_multiplication _ M.

  Definition monoid_to_disp_Monad_data_CAT : disp_Monad_data x := μ ,, η.

  Lemma monoid_to_disp_Monad_laws_CAT : disp_Monad_laws monoid_to_disp_Monad_data_CAT.
  Proof.
    repeat split.
    - intro c.
      set (t := monoid_right_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_left_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_assoc_law _ M).
      refine (! (toforallpaths _ _ _ (base_paths _ _ t) c) @ _).
      etrans.
      + apply assoc'.
      + apply id_left.
  Qed.

  Definition monoid_to_monad_CAT : Monad
    := _ ,, _ ,, monoid_to_disp_Monad_laws_CAT.

End OnObjects.

  Lemma monoid_to_monad_map_is_monad_mor {M M' : Monoid} (f : M --> M')
    : disp_Monad_Mor_laws (monoid_to_disp_Monad_data_CAT M) (monoid_to_disp_Monad_data_CAT M') (pr1 f).
  Proof.
    induction f as [f [H1 H2]]; split; intro A; cbn in f, H1, H2 |- *.
    {
      etrans.
      use (!maponpaths (λ x, pr1 x A) H1).
      use (maponpaths (λ x, x · _)).
      etrans.
      refine (maponpaths (λ x , pr1 x A) _).
      use vcomp_whisker_CAT.
      easy.
    }
    use (maponpaths (λ x, pr1 x A) H2).
  Qed.

  Definition monoid_to_monad_map
    (M M' : Monoid)
    (f : M --> M') : monoid_to_monad_CAT M --> monoid_to_monad_CAT M'
    := pr1 f ,, monoid_to_monad_map_is_monad_mor f.


  Definition monoid_to_monad_functor_data
    : functor_data Monoid Monad
    := make_functor_data monoid_to_monad_CAT monoid_to_monad_map.

  Lemma monoid_to_monad_is_functor
    : is_functor monoid_to_monad_functor_data.
  Proof.
    split.
    - intro M.
      use subtypePath; [|easy].
      use isaprop_disp_Monad_Mor_laws.
    - intros M1 M2 M3 f g.
      use subtypePath; [|easy].
      use isaprop_disp_Monad_Mor_laws.
  Qed.

  Definition monoid_to_monad_functor
    : Monoid ⟶ Monad
    := make_functor monoid_to_monad_functor_data monoid_to_monad_is_functor.

End MonoidToMonad.

Section MonadToMonoid.

Section OnObjects.
  Context (M : Monad).

  Definition monad_to_monoid_CAT_data : monoid_data EndC (functor_from_Monad M)
    := μ M ,, η M.

  Lemma monad_to_monoid_CAT_laws :  monoid_laws EndC monad_to_monoid_CAT_data.
  Proof.
    split3; apply (nat_trans_eq C); intro c; cbn.
    - apply Monad_law2.
    - apply Monad_law1.
    - rewrite id_left. apply pathsinv0, Monad_law3.
  Qed.

  Definition monad_to_monoid_CAT_disp : monoid EndC (functor_from_Monad M)
    := monad_to_monoid_CAT_data,,monad_to_monoid_CAT_laws.

  Definition monad_to_monoid_CAT : Monoid
    := _,,monad_to_monoid_CAT_disp.

End OnObjects.

  Lemma monad_to_monoid_map_is_monoid_mor {M M' : Monad} (f : M --> M')
    : is_monoid_mor _ (monad_to_monoid_CAT_disp M) (monad_to_monoid_CAT_disp M') (pr1 f).
  Proof.
    induction f as [f [H1 H2]]; split; (apply nat_trans_eq; [apply homset_property|]).
    - intro A; cbn.
      etrans; [|use (!H1 A)].
      use (maponpaths (λ x, x · _)).
      use nat_trans_ax.
    - exact H2.
  Qed.

  Definition monad_to_monoid_map
    (M M' : Monad)
    (f : M --> M') : monad_to_monoid_CAT M --> monad_to_monoid_CAT M'
    := pr1 f ,, monad_to_monoid_map_is_monoid_mor f.

  Definition monad_to_monoid_functor_data
    : functor_data Monad Monoid
    := make_functor_data monad_to_monoid_CAT monad_to_monoid_map.

  Lemma monad_to_monoid_is_functor
    : is_functor monad_to_monoid_functor_data.
  Proof.
    split.
    - intro M.
      apply MON_mor_eq; easy.
    - intros M1 M2 M3 f g.
      apply MON_mor_eq; easy.
  Qed.

  Definition monad_to_monoid_functor
    : Monad ⟶ Monoid
    := make_functor monad_to_monoid_functor_data monad_to_monoid_is_functor.

End MonadToMonoid.

Lemma monoid_to_monad_to_monoid
  (M : category_of_monoids_in_monoidal_cat (monendocat_monoidal C))
  : monad_to_monoid_CAT (monoid_to_monad_CAT M) = M.
Proof.
  use total2_paths_f; [easy|].
  use total2_paths_f; [easy|].
  use proofirrelevance.
  use isaprop_monoid_laws.
Defined.

Lemma monad_to_monoid_to_monad
  (M : Monad)
  : monoid_to_monad_CAT (monad_to_monoid_CAT M) = M.
Proof.
  use total2_paths_f; [easy|].
  use total2_paths_f; [easy|].
  use proofirrelevance.
  use isaprop_disp_Monad_laws.
Defined.

Lemma monad_to_monoid_functor_fully_faithful
  : fully_faithful monad_to_monoid_functor.
Proof.
  intros M M' f; use make_iscontr; cbn.
  - use tpair.
    + change (M --> M').
      use (transportf (λ x, x --> _)); [|use monad_to_monoid_to_monad|].
      use (transportf (λ x, _ --> x)); [|use monad_to_monoid_to_monad|].
      now use monoid_to_monad_map.
    + abstract (
        use subtypePath;
        [intro; use isaprop_is_monoid_mor|];
        simpl; do 2 (rewrite transportf_total2; simpl);
        etrans;
        [use maponpaths|];
        [exact (pr1 f)| |];
        [use (transportf_total2_paths_f _ _ _ (pr1 f))|];
        use (transportf_total2_paths_f (λ x, pr1 x ⟹  pr11 M'))
      ).
  - intros [g g_hyp].
    use subtypePath.
    { intro; use isaset_total2.
      + use isaset_nat_trans; use homset_property.
      + intro; use isasetaprop; use isaprop_is_monoid_mor. }
    use subtypePath.
    { intro; use isaprop_disp_Monad_Mor_laws. }
    use subtypePath.
    { intro; use isaprop_is_nat_trans; use homset_property. }
    simpl; do 2 rewrite transportf_total2.
    unfold nat_trans; simpl; do 2 rewrite transportf_total2; simpl.
    rewrite <- g_hyp; simpl.
    use pathsinv0; etrans.
    { apply maponpaths.
      use (transportf_total2_paths_f (B := λ x, ∑ (T : disp_Monad_data x), disp_Monad_laws T) 
        (λ x, nat_trans_data (pr11 M) (pr1 x))). }
    use (transportf_total2_paths_f (B := λ x, ∑ (T : disp_Monad_data x), disp_Monad_laws T) 
      (λ x, nat_trans_data (pr1 x) (pr11 M'))).
Qed.

Lemma monad_to_monoid_functor_isweq
  : isweq monad_to_monoid_functor.
Proof.
  use (weqproperty (weq_iso monad_to_monoid_CAT monoid_to_monad_CAT _ _)).
  - intro R. use pair_path_in2.
    use subtypePath; [|easy].
    intro; use isaprop_disp_Monad_laws.
  - intro R. use pair_path_in2.
    use subtypePath; [|easy];
    intro; use isaprop_monoid_laws.
Qed.

Definition monad_iso_monoid_endcat
  : catiso Monad Monoid.
Proof.
  exists (monad_to_monoid_functor).
  split.
  - exact monad_to_monoid_functor_fully_faithful.
  - exact monad_to_monoid_functor_isweq.
Defined.

(** 2. Monad modules and monoid modules are isomorphic *)
Section FixAMonoid.
  (* We show that monad left modules are isomorphic to monoid left-modules, that is, right-modules for the swapped monoidal product *)

  Context (monoid' : Monoid).
  Let monad : Monad := monoid_to_monad_CAT monoid'.
  Let monoid : Monoid_swapped := monoid_to_monoid_swapped_mon EndC monoid'.

  Let monoidModule : category := MOD (pr1 monoid) (pr2 monoid).
  Let monadModule : category := category_LModule monad C.

  Section FixAMonadModule.
    Context (monad_module : monadModule).
    Let M : C ⟶  C := pr11 monad_module.
    Let bind : pr1 monad ∙ M ⟹  M := pr21 monad_module.

    Lemma monad_to_monoid_modules_laws
      : module_laws _ (pr2 monoid) bind.
    Proof.
      split.
      - apply nat_trans_eq; [use homset_property |]; cbn; intro.
        rewrite id_left.
        use LModule_law2.
      - apply nat_trans_eq; [use homset_property |]; cbn; intro.
        use LModule_law1.
    Qed.

    Definition monad_to_monoid_modules
      : monoidModule
      := M ,, bind ,, monad_to_monoid_modules_laws.
  End FixAMonadModule.

  Section FixAMonadModuleMorphism.
    Context (monad_module : monadModule).
    Let M : C ⟶  C := pr11 monad_module.
    Let bind : pr1 monad ∙ M ⟹  M := pr21 monad_module.

    Context (monad_module' : monadModule).
    Let M' : C ⟶  C := pr11 monad_module'.
    Let bind' : pr1 monad ∙ M' ⟹  M' := pr21 monad_module'.

    Context (f : monad_module --> monad_module').

    Lemma monad_to_monoid_modules_map_is_module_mor
      : is_module_mor _ (pr2 monoid)
        (pr2 (monad_to_monoid_modules monad_module))
        (pr2 (monad_to_monoid_modules monad_module'))
        (pr1 f).
    Proof.
      apply nat_trans_eq; [use homset_property |]; cbn.
      use (pr2 f).
    Qed.

    Definition monad_to_monoid_modules_map
      : monad_to_monoid_modules monad_module --> monad_to_monoid_modules monad_module'
      := pr1 f ,, monad_to_monoid_modules_map_is_module_mor.
  End FixAMonadModuleMorphism.


  Definition monad_to_monoid_modules_functor_data
    : functor_data monadModule monoidModule
    := monad_to_monoid_modules ,,  monad_to_monoid_modules_map.

  Lemma monad_to_monoid_modules_functor_laws
    : is_functor monad_to_monoid_modules_functor_data.
  Proof.
    split; repeat intro; apply MOD_mor_eq; easy.
  Qed.

  Definition monad_to_monoid_modules_functor
    : monadModule ⟶ monoidModule
    := make_functor monad_to_monoid_modules_functor_data monad_to_monoid_modules_functor_laws.

  Section FixAMonoidModule.
    Context (monoid_module : monoidModule).
    Let M : C ⟶  C := pr1 monoid_module.
    Let bind : pr1 monad ∙ M ⟹  M := pr12 monoid_module.

    Lemma monoid_to_monad_modules_laws
      : LModule_laws monad (M,, bind).
    Proof.
      split.
      - intro; cbn.
        use (maponpaths (λ f, pr1 f c) (module_laws_unit_from_module _ _ (pr2 monoid_module))).
      - intro; cbn.
        symmetry; rewrite <- id_left, assoc; symmetry.
        use (maponpaths (λ f, pr1 f c) (module_laws_assoc_from_module _ _ (pr2 monoid_module))).
    Qed.

    Definition monoid_to_monad_modules : monadModule
      := (M ,, bind) ,, monoid_to_monad_modules_laws.
  End FixAMonoidModule.

  Section FixAMonoidModuleMorphism.
    Context (monoid_module : monoidModule).
    Let M : C ⟶  C := pr1 monoid_module.
    Let bind : pr1 monad ∙ M ⟹  M := pr12 monoid_module.

    Context (monoid_module' : monoidModule).
    Let M' : C ⟶  C := pr1 monoid_module'.
    Let bind' : pr1 monad ∙ M' ⟹  M' := pr12 monoid_module'.

    Context (f : monoid_module --> monoid_module').

    Definition monoid_to_monad_modules_map
      : monoid_to_monad_modules monoid_module --> monoid_to_monad_modules monoid_module'.
    Proof.
      exists (pr1 f).
      abstract (
        intro x; exact (maponpaths (λ g, pr1 g x) (pr2 f))
      ).
    Defined.
  End FixAMonoidModuleMorphism.

  Definition monoid_to_monad_modules_functor_data
    : functor_data monoidModule monadModule
    := monoid_to_monad_modules ,, monoid_to_monad_modules_map.

  Lemma monoid_to_monad_modules_functor_laws
    : is_functor monoid_to_monad_modules_functor_data.
  Proof.
    split; repeat intro;
      apply LModule_Mor_equiv; easy.
  Qed.

  Definition monoid_to_monad_modules_functor
    : monoidModule ⟶ monadModule
    := make_functor monoid_to_monad_modules_functor_data monoid_to_monad_modules_functor_laws.

  Lemma monad_to_monoid_modules_functor_fully_faithful
    : fully_faithful monad_to_monoid_modules_functor.
  Proof.
    intros M M'.
    use (weqproperty (weq_iso (monad_to_monoid_modules_map M M')
      (monoid_to_monad_modules_map _ _) _ _)); cbn.
    - intro X; use subtypePath.
      { intro; use impred_isaprop; intro; use homset_property. }
      reflexivity.
    - intro X; use subtypePath.
      { intro; use isaprop_is_module_mor. }
      reflexivity.
  Qed.

  Lemma monad_to_monoid_modules_functor_is_weq
    : isweq monad_to_monoid_modules_functor.
  Proof.
    use (weqproperty (weq_iso monad_to_monoid_modules monoid_to_monad_modules _ _)).
    - intro X.
      use subtypePath.
      { intro; use isaprop_LModule_laws. }
      reflexivity.
    - intro X.
      use pair_path_in2.
      use subtypePath.
      { intro. use isaprop_module_laws. }
      reflexivity.
  Qed.

  Definition monad_modules_iso_monoid_modules_endcat
    : catiso monadModule monoidModule.
  Proof.
    exists monad_to_monoid_modules_functor.
    split.
    - exact monad_to_monoid_modules_functor_fully_faithful.
    - exact monad_to_monoid_modules_functor_is_weq.
  Defined.

End FixAMonoid.
End FixACategory.
