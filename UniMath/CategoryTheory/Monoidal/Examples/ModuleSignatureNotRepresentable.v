Require Import UniMath.MoreFoundations.All.

(* Require Import UniMath.Tactics.EnsureStructuredProofs. *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.ModelsOfModuleSignature.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.

Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.BinCoproducts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope mor_disp_scope.


Section SomeSignaturesAreNotRepresentable.

  (* Define C to be the monoidal category [Set, Set] 
     with (usual) composition as monoidal bifunctor:
     F ∘ G = F ⊗ G *)

  (* The definition of monendocat_monoidal_cat uses the diagrammatic composition "·" rather than "∘" *)
  Let C : monoidal_cat := _ ,, monoidal_swapped (monendocat_monoidal_cat SET).

  (* Simple consequence of [preserves_colimit_pre_composition_functor] *)
  Local Lemma precomp_preserves_bincoproduct (Z : C)
    : preserves_bincoproduct (rightwhiskering_functor C Z).
  Proof.
    intros A B AB i1 i2 h.
    use limits_isBinCoproduct_from_isBinCoproductCocone.
    eassert _ as h' by exact (limits_isBinCoproductCocone_from_isBinCoproduct _ _ _ h).
    eassert _ as q by exact (preserves_colimit_pre_composition_functor Z _ _ _ (λ _, ColimCoconeHSET _ _) h').
    cbn.
    intros X [cc_X cc_X'].
    transparent assert (cc : (cocone (mapdiagram (pre_composition_functor SET SET SET Z)
        (bincoproduct_diagram A B)) X)).
    { use make_cocone; cbn.
      - intro b; induction b.
        + use (cc_X true).
        + use (cc_X false).
      - abstract (intros ? ? e; induction e). }
    specialize (q X cc); induction q as [[q1 q2] q3]; cbn in q1, q2, q3.
    use ((q1 ,, _),, _); cbn.
    - abstract (intro b; induction b; [use (q2 true)|use (q2 false)]).
    - intros [α α_hyp].
      use subtypePath.
      { intro x. use (isaprop_is_cocone_mor _ _ (x : C⟦AB ⊗ Z, X⟧)). }
      cbn.
      assert (is_cocone_mor
        (mapcocone (pre_composition_functor SET SET SET Z)
           (bincoproduct_diagram A B) (CopCocone i1 i2))
        cc α) as α_hyp'.
      { intro b; induction b; cbn.
        - use (α_hyp true).
        - use (α_hyp false). } 
      use (maponpaths pr1 (q3 (α ,, α_hyp'))).
  Qed.

  (* Define Σ := 𝒫 ∘ Θ where 𝒫 is the (covariant) powerset functor *)
  Definition example_module_signature_not_representable_signature 
    : module_signature_cat
    := @product_signature C trivial_signature powerset_functor.

  Let Σ := example_module_signature_not_representable_signature.

  Section AssumeItWasRepresentable.
    Context (hyp : is_representable Σ).

    Let Σ̅ := InitialObject hyp.

    (* We rely on the result that initial models are fixed points of the I + Σ(-) functor *)
    Local Definition iter_signature_initial
      := initial_model_fixpoint 
          example_module_signature_not_representable_signature
          (BinCoproducts_functor_precat _ _ BinCoproductsHSET) 
          precomp_preserves_bincoproduct
          hyp.

    (* The model Σ̅' has I + Σ(Σ̅) as underlying object in C *)
    Let Σ̅' := iter_model Σ (BinCoproducts_functor_precat _ _ BinCoproductsHSET)
        precomp_preserves_bincoproduct Σ̅.

    (* By fixed point, we have an iso I + Σ(Σ̅) ≅ Σ̅ (of models) *)
    Local Definition iter_signature_iso : z_iso Σ̅ Σ̅'
      := ziso_Initials hyp (make_Initial _ iter_signature_initial).

    (* A contradiction should work for any choice of X *)
    (* but choosing X = ∅ simplifies the proof *)
    Let X_set : SET := emptyHSET. 
    Let X : UU := pr1 X_set.

    Local Definition eval_at_X : [SET,SET] ⟶  SET
      := rightwhiskering_functor (bifunctor_from_functorfromproductcat evaluation_functor) X_set.

    (* We map the iso of models to an iso of sets by relying on the functor *)
    Local Definition forgetful 
      : models_of_module_signatures_cat Σ ⟶  SET
      := pr1_category _ ∙ (pr1_category _ ∙ eval_at_X).

    Local Definition iter_signature_iso_of_sets
      : z_iso (forgetful Σ̅) (forgetful Σ̅')
      := functor_on_z_iso forgetful iter_signature_iso.

    Let Σ̅X : UU := pr1 (pr111 Σ̅ X_set).

    (* We have Σ̅X ≃ X + 𝒫(Σ̅X), and since X = ∅, Σ̅X ≃ 𝒫(Σ̅X) *)
    Local Definition bijection_of_sets
      : Σ̅X ≃ subtype_set (Σ̅X).
    Proof.
      eapply weqcomp.
      - exact (hset_z_iso_equiv _ _ iter_signature_iso_of_sets).
      - apply invweq; exact (weqii2withneg _ (λ x, x)).
    Defined.

    (* It induces a surjection Σ̅X ↠ 𝒫(Σ̅X) *)
    (* In general, no matter the choice of X, we obtain such a surjection *)
    Local Definition surjection_of_sets
      : issurjective bijection_of_sets.
    Proof.
      use issurjectiveweq.
      use weqproperty.
    Qed.

    (* This surjection contradicts Cantor's theorem *)
    Lemma contradiction : empty.
    Proof.
      use (cantor_no_surjection_powerset _ _ surjection_of_sets).
    Qed.
  End AssumeItWasRepresentable.

  Theorem example_module_signature_not_representable
    : ¬ is_representable example_module_signature_not_representable_signature.
  Proof.
    use contradiction.
  Qed.
End SomeSignaturesAreNotRepresentable.

