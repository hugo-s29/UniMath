Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
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
  : split_coequalizer f g → split_coequalizer (# F f) (#F g).
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

Section CatIsoStrictlyCreatesCoequalizers.
  Local Open Scope mor_disp_scope.
  Context {C : category} 
          {disp_D disp_D' : disp_cat C}
          (loc_D : locally_propositional disp_D)
          (loc_D' : locally_propositional disp_D')
          (F : disp_functor (functor_identity C) disp_D disp_D')
          (F_hyp : disp_functor_iso F)
          (hyp : strictly_creates_coequalizers_of_U_split_pairs disp_D).

  Local Definition G : disp_functor (functor_identity C) disp_D' disp_D.
  Proof.
    exists (disp_functor_iso_inverse_data F_hyp).
    abstract (split; intros; use proofirrelevance; use loc_D).
  Defined.

  Local Lemma FG_ob_is_identity (c : C) (d : disp_D' c)
    : F c (G c d) = d.
  Proof.
    use homotweqinvweq.
  Qed.

  Local Lemma GF_ob_is_identity (c : C) (d : disp_D c)
    : G c (F c d) = d.
  Proof.
    use homotweqinvweq.
  Qed.

  Opaque G.

  Local Definition G_hyp : disp_functor_iso G.
  Proof.
    split.
    - intros x y xx yy f.
      use isweqimplimpl.
      + intro m; cbn in m.
        refine (transportf (λ u, u -->[ f ] _) (FG_ob_is_identity _ _) _).
        refine (transportf (λ u, _ -->[ f ] u) (FG_ob_is_identity _ _) _).
        exact (♯ F m).
      + use loc_D'.
      + use loc_D.
    - intro x.
      use (weqproperty (weq_iso _ _ _ _)).
      + use (F x).
      + intro xx; use FG_ob_is_identity.
      + intro xx; use GF_ob_is_identity.
  Qed.

  Section FixASplitCoequalizer.
    Context (c c' : C) (d : disp_D' c) (d' : disp_D' c').
    Context (f g : C ⟦ c, c' ⟧) (f' : d -->[ f ] d') (g' : d -->[ g ] d').
    Context (p : split_coequalizer f g).

    Let Z := split_coequalizer_ob p.
    Let h := split_coequalizer_arrow p.

    Let Gd : disp_D c := G c d.
    Let Gd' : disp_D c' := G c' d'.
    Let Gf : Gd -->[ f ] Gd' := ♯G f'.
    Let Gg : Gd -->[ g ] Gd' := ♯G g'.

    Let f_tot : total_category disp_D'⟦ c ,, d , c' ,, d' ⟧ := f ,, f'.
    Let g_tot : total_category disp_D'⟦ c ,, d , c' ,, d' ⟧ := g ,, g'.

    Let Gf_tot : total_category disp_D⟦ c ,, Gd , c' ,, Gd' ⟧ := f ,, Gf.
    Let Gg_tot : total_category disp_D⟦ c ,, Gd , c' ,, Gd' ⟧ := g ,, Gg.

    Let GZ : disp_D Z := pr1 (iscontrpr1 (hyp _ _ Gf_tot Gg_tot p)).
    Let Gh : Gd' -->[ h ] GZ := pr12 (iscontrpr1 (hyp _ _ Gf_tot Gg_tot p)).

    Let Gh_tot : total_category disp_D⟦ c' ,, Gd' , Z ,, GZ ⟧ := h ,, Gh.

    Local Definition z_structure : disp_D' Z := F Z GZ.

    Local Lemma GZ_is_GZ : GZ = G Z z_structure.
    Proof.
      use pathsinv0; use GF_ob_is_identity.
    Qed.

    Local Definition h_structure : d' -->[ h ] z_structure.
    Proof.
      refine (transportf (λ u, u -->[ h ] _) (FG_ob_is_identity _ _) _).
      refine (♯ F Gh).
    Defined.

    Let h_tot : total_category disp_D'⟦ c' ,, d' , Z ,, z_structure ⟧ := h ,, h_structure.

    Local Lemma coeq_eq : f_tot · h_tot = g_tot · h_tot.
    Proof.
      use (mor_eq_total_category_when_locally_prop loc_D'); cbn.
      exact (maponpaths pr1 (pr122 (iscontrpr1 (hyp _ _ Gf_tot Gg_tot p)))).
    Qed.

    Local Lemma h_is_coequalizer
      : isCoequalizer f_tot g_tot h_tot coeq_eq.
    Proof.
      use make_isCoequalizer; intros [c'' d''] [k k'] eq; cbn in k, k', eq.
      assert (Gf_tot · Gh_tot = Gg_tot · Gh_tot) as Geq
      by exact (pr122 (iscontrpr1 (hyp _ _ Gf_tot Gg_tot p))).
      assert (isCoequalizer Gf_tot Gg_tot Gh_tot Geq) as coeq
      by exact (pr222 (iscontrpr1 (hyp _ _ Gf_tot Gg_tot p))).

      transparent assert (Gk_tot : (total_category disp_D ⟦ c',, Gd', c'',, G c'' d'' ⟧)).
      { exists k; exact (♯ G k'). }

      assert (Gf_tot · Gk_tot = Gg_tot · Gk_tot) as Gk_eq.
      { use (mor_eq_total_category_when_locally_prop loc_D); use (maponpaths pr1 eq). }

      specialize (coeq _ _ Gk_eq).
      pose (ψ_C := pr11 (iscontrpr1 coeq)).
      pose (ψ_D := pr21 (iscontrpr1 coeq)).
      cbn in ψ_C, ψ_D; fold ψ_C in ψ_D.

      use unique_exists.
      - exists ψ_C; cbn.
        refine (transportf (λ u, u -->[ ψ_C ] _) (FG_ob_is_identity _ _) _).
        refine (transportf (λ u, _ -->[ ψ_C ] u) (FG_ob_is_identity _ _) _).
        refine (transportf (λ u, F Z u -->[ _ ] _) GZ_is_GZ _).
        use (♯ F ψ_D).
      - abstract (
          use (mor_eq_total_category_when_locally_prop loc_D');
          exact (maponpaths pr1 (pr2 (iscontrpr1 coeq)))
        ).
      - abstract (intros ?; use homset_property).
      - abstract (
          intros [ϕ ϕ'] eq'; cbn in ϕ, ϕ', eq';
          use (mor_eq_total_category_when_locally_prop loc_D'); cbn;
          transparent assert (ϕ_tot' : (total_category disp_D ⟦ Z,, GZ, c'',, G c'' d'' ⟧));
          [exists ϕ; cbn|];
          [refine (transportb (λ u, u -->[ _ ] _) GZ_is_GZ _)|];
          [exact (♯ G ϕ')|];
          use (maponpaths pr1 (path_to_ctr _  _ coeq ϕ_tot' _));
          use (mor_eq_total_category_when_locally_prop loc_D); 
          use (maponpaths pr1 eq')
        ).
    Qed.

    Context (z_structure' : disp_D' Z).
    Context (h_structure' : d' -->[ h] z_structure').

    Let h_tot' : total_category disp_D'⟦ c' ,, d' , Z ,, z_structure' ⟧ := h ,, h_structure'.

    Context (eq' : f_tot · h_tot' = g_tot · h_tot').
    Context (coeq : isCoequalizer f_tot g_tot h_tot' eq').

    Let Gh' : Gd' -->[ h ] G Z z_structure' := ♯ G h_structure'.
    Let Gh_tot' : total_category disp_D⟦ c' ,, Gd' , Z ,, G _ z_structure' ⟧ := h ,, Gh'.

    Local Lemma coeq_eq' 
      : Gf_tot · Gh_tot' = Gg_tot · Gh_tot'.
    Proof.
      use (mor_eq_total_category_when_locally_prop loc_D).
      use (maponpaths pr1 eq').
    Qed.

    Local Lemma h'_is_coequalizer
      : isCoequalizer Gf_tot Gg_tot Gh_tot' coeq_eq'.
    Proof.
      use make_isCoequalizer; intros [c'' d''] [k k'] eq; cbn in k, k', eq.
      transparent assert (Fk_tot : (total_category disp_D' ⟦ c',, d', c'',, F c'' d'' ⟧)).
      { exists k.
        refine (transportf (λ u, u -->[ k ] _) (FG_ob_is_identity _ _) _).
        exact (♯ F k'). }
      assert (f_tot · Fk_tot = g_tot · Fk_tot) as Fk_hyp.
      { use (mor_eq_total_category_when_locally_prop loc_D'); use (maponpaths pr1 eq). }
      specialize (coeq _ _ Fk_hyp).
      use unique_exists; simpl.
      - exists (pr11 (iscontrpr1 coeq)).
        refine (transportf (λ u, _ -->[ _ ] u) (GF_ob_is_identity _ _) _).
        exact (♯ G (pr21 (iscontrpr1 coeq))).
      - use subtypePath.
        { intro; use loc_D. }
        { use (maponpaths pr1 (pr2 (iscontrpr1 coeq))). }
      - intro.
        eassert (∏ (u v : C) (uu : disp_D u) (vv : disp_D v), isaset (∑ x, uu -->[ x ] vv)) as q
        by (
          intros u v uu vv;
          pose (uuu := u ,, uu : total_category disp_D);
          pose (vvv := v ,, vv : total_category disp_D);
          use (homset_property (total_category disp_D) uuu vvv)
        ); use q.
      - intros [y y'] y_eq.
        use subtypePath.
        { intro; use loc_D. }
        cbn.
        transparent assert (a : (total_category disp_D' ⟦ Z,, z_structure', c'',, F c'' d'' ⟧)).
        { exists y; cbn.
          refine (transportf (λ u, u -->[ y ] _) (FG_ob_is_identity _ _) _).
          use (♯ F y'). }
        assert (a_hyp : h_tot' · a = Fk_tot).
        { use (mor_eq_total_category_when_locally_prop loc_D').
          use (maponpaths pr1 y_eq). }
        use (maponpaths pr1 (path_to_ctr _ _ coeq _ a_hyp)).
    Qed.
  
    Local Lemma z_structure_unique
      : z_structure' = z_structure.
    Proof.
      unfold z_structure; cbn.
      refine (!_ @ _).
      { use FG_ob_is_identity. }
      { apply maponpaths; unfold GZ.
        eapply (path_to_ctr _ _ (hyp _ _ Gf_tot Gg_tot p)).
        do 2 eexists; use h'_is_coequalizer. }
    Qed.
  End FixASplitCoequalizer.


  Proposition strictly_creates_coequalizers_of_U_split_pairs_catiso_one_side
    : strictly_creates_coequalizers_of_U_split_pairs disp_D'.
  Proof.
    intros [c d] [c' d'] [f f'] [g g'] p; cbn.
    use make_iscontr.
    - do 3 eexists; use h_is_coequalizer.
    - abstract (
        intros [z_structure' [h_structure' [eq' coeq']]];
        use subtypePath; [|now use z_structure_unique];
        intro; use isaproptotal2;
        [intro; use isaproptotal2|];
        [intro; use isaprop_isCoequalizer| |];
        intros; use proofirrelevance; [|use loc_D'];
        eassert (∏ (u v : C) (uu : disp_D' u) (vv : disp_D' v), isaset (∑ x, uu -->[ x ] vv)) as q
        by (
          intros u v uu vv;
          pose (uuu := u ,, uu : total_category disp_D');
          pose (vvv := v ,, vv : total_category disp_D');
          use (homset_property (total_category disp_D') uuu vvv)
        ); use q
      ).
  Defined.
End CatIsoStrictlyCreatesCoequalizers.

Proposition strictly_creates_coequalizers_of_U_split_pairs_catiso
  {C : category} {disp_D disp_D' : disp_cat C} 
  (loc_D : locally_propositional disp_D) (loc_D' : locally_propositional disp_D')
  (F : disp_functor (functor_identity C) disp_D disp_D') (F_hyp : disp_functor_iso F)
  : strictly_creates_coequalizers_of_U_split_pairs disp_D 
  ≃ strictly_creates_coequalizers_of_U_split_pairs disp_D'.
Proof.
  use weqiff; try use isaprop_strictly_creates_coequalizers_of_U_split_pairs.
  split.
  - now use strictly_creates_coequalizers_of_U_split_pairs_catiso_one_side.
  - now use (strictly_creates_coequalizers_of_U_split_pairs_catiso_one_side _ _ _ (G_hyp _ _ _ _)).
Defined.
        
Section MonadicAdjunctions.
  Context {C : category}.
  Context {disp_D : disp_cat C} (loc_D : locally_propositional disp_D).
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

  Definition comparison_disp_functor_data 
    : disp_functor_data (functor_identity C) disp_D (Algebra_disp_cat T).
  Proof.
    use tpair.
    - intros c d; use (_ ,, _ ,, _).
      + exact (pr1 (counit_from_are_adjoints adj (c ,, d))).
      + abstract use (triangle_id_right_ad adj (c ,, d)).
      + abstract use (!maponpaths pr1 (nat_trans_ax (counit_from_are_adjoints adj)
            _ _ (counit_from_are_adjoints adj (c,, d)))).
    - intros c c' d d' f f'.
      abstract use (!maponpaths pr1 (nat_trans_ax (counit_from_are_adjoints adj)
          (c ,, d) (c' ,, d') (f ,, f'))).
  Defined.

  Lemma comparison_disp_functor_is_functor
    : disp_functor_axioms comparison_disp_functor_data.
  Proof.
    split; intros; use proofirrelevance; use homset_property.
  Qed.

  Definition comparison_disp_functor 
    : disp_functor (functor_identity _) disp_D (Algebra_disp_cat T).
  Proof.
    use tpair.
    - exact comparison_disp_functor_data.
    - exact comparison_disp_functor_is_functor.
  Defined.

  Definition is_strict_monadic 
    := disp_functor_iso comparison_disp_functor.

  Lemma isaprop_is_strict_monadic
    : isaprop is_strict_monadic.
  Proof.
    use isapropdirprod.
    - use isaprop_disp_functor_ff.
    - use impred_isaprop; intro; use isapropisweq.
  Qed.

  Theorem strict_monadicity_theorem_1 
    : is_strict_monadic → strictly_creates_coequalizers_of_U_split_pairs disp_D.
  Proof.
    intro hyp.
    refine (invmap _ (forgetful_algebra_functor_creates_coequalizers_of_U_split_pairs T)).
    use strictly_creates_coequalizers_of_U_split_pairs_catiso.
    - exact loc_D.
    - exact (Algebra_disp_cat_locally_propositional T).
    - exact comparison_disp_functor.
    - exact hyp.
  Qed.

End MonadicAdjunctions.
