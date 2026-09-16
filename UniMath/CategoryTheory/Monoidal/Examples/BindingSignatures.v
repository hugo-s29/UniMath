Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Categories.HSET.All.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.SignaturesWithStrength.

Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope stn.

Section SignatureBinding.
  Context (n : nat).

  Let EndSET : monoidal_cat := _ ,, monendocat_monoidal SET.

  Definition plus_n_functor_data : functor_data SET SET.
  Proof.
    use tpair.
    - intro X. exists (pr1 X ⨿ ⟦ n ⟧).
      exact (isasetcoprod _ _ (pr2 X) (isasetstn n)).
    - intros X Y f [x | k]; cbn in *.
      * use (inl (f x)).
      * use (inr k).
  Defined.

  Lemma plus_n_functor_is_functor
    : is_functor plus_n_functor_data.
  Proof.
    split.
    - intros ?; use funextsec; intros [? | ?]; use idpath.
    - intros ? ? ? ? ?; use funextsec; intros [? | ?]; use idpath.
  Qed.

  Definition plus_n_functor : SET ⟶ SET
    := make_functor _ plus_n_functor_is_functor.

  Definition binding_n_variables_functor_data : functor_data EndSET EndSET.
  Proof.
    use tpair.
    - intro X; exact (X ∙ plus_n_functor).
    - intros X Y α; use (post_whisker α).
  Defined.

  Lemma binding_n_variables_functor_is_functor
    : is_functor binding_n_variables_functor_data.
  Proof.
    split.
    - intros ?.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_nat_trans; use homset_property.
      use funextsec; intros ?.
      use funextsec; now intros [? | ?].
    - intros ? ? ? ? ?.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_nat_trans; use homset_property.
      use funextsec; intros ?.
      use funextsec; now intros [? | ?].
  Qed.

  Definition binding_n_variables_functor : EndSET ⟶ EndSET
    := make_functor _ binding_n_variables_functor_is_functor.
  
  Example binding_n_variables_strength 
    : strength_for_signature binding_n_variables_functor.
  Proof.
    use make_strength_for_signature.
    - intros X (B, b); simpl in b; use make_nat_trans.
      * intro. simpl.
        intro.

  Example binding_n_variables_signature_with_strength 
    : @signature_with_strength_cat (_ ,, EndSET). 
  Proof.


End SignatureBinding.
