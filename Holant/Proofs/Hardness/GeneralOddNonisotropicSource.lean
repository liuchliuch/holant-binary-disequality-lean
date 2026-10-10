import Holant.Proofs.Hardness.GeneralOddNonisotropicDescent

/-! Original-family nonisotropic producer. Failure of the literal Tract
predicate supplies an original row with support off the unary's axis; the
actual cap descent then produces an endpoint-support graph internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicSource
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
open GeneralOddNonisotropicFrame GeneralOddNonisotropicDescent GeneralOddUnarySource
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A pure endpoint tensor has an explicit decomposition into unary rows. -/
theorem purePin_tensor (n : ℕ) (c : AlgebraicComplex) (hc : c≠0) :
    Signature.TensorClosure (fun m _ => m=1 ∨ m=2) (purePin c false n) := by
  let D : TensorDecomposition AlgebraicComplex n := {
    count := n
    arity := fun _ => 1
    factor := fun _ x => if x 0=false then 1 else 0
    ports := {
      toFun := fun p => p.1
      invFun := fun i => ⟨i,0⟩
      left_inv := by
        intro p
        rcases p with ⟨i,j⟩
        have hj : j=0 := Subsingleton.elim _ _
        subst j
        rfl
      right_inv := fun _ => rfl }
    scale := Units.mk0 c hc }
  refine ⟨D,fun _ => Or.inl rfl,?_⟩
  funext x
  change c*(∏ i : Fin n,if x i=false then (1 : AlgebraicComplex) else 0)=_
  rw [Fintype.prod_boole]
  simp only [←funext_iff]
  by_cases hx : x=(fun _ => false) <;> simp [purePin,hx]

/-- One-dimensional support in the invertible frame is a tensor product of
unaries in the original coordinates, including its exact nonzero scale. -/
theorem axis_tensor (u : Signature AlgebraicComplex 1) (hu : norm u≠0)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (haxis : ∀ x,chart u f x≠0 → x=(fun _ => false)) :
    SourceTensorClosure (fun m _ => m=1 ∨ m=2) f := by
  classical
  by_cases hf : f=0
  · exact Or.inl hf
  have he : chart u f=purePin (chart u f (fun _ => false)) false n := by
    funext x
    by_cases hx : x=(fun _ => false)
    · simp [purePin,hx]
    · have hz : chart u f x=0 := by
        by_contra hz
        exact hx (haxis x hz)
      simp [purePin,hx,hz]
  have hc : chart u f (fun _ => false)≠0 := by
    intro hz
    apply hf
    apply chart_injective u hu
    rw [he,hz]
    funext x
    simp [purePin,chart,Signature.coordinateAction_zero]
  have ht := Signature.TensorClosure.map_action
    (D:=fun m (_ : Signature AlgebraicComplex m) => m=1 ∨ m=2)
    (inverse u) (fun _ _ h => h) (purePin_tensor n _ hc)
  rw [←he] at ht
  have hcanc : Signature.coordinateAction (fun _ => inverse u) (chart u f)=f :=
    Signature.coordinateAction_cancel _ _ (fun _ => inverse_frame u hu) f
  rw [hcanc] at ht
  exact Or.inr ht

theorem all_axis_tract (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (u : Signature AlgebraicComplex 1) (hu : norm u≠0)
    (haxis : ∀ f∈preprocess F,∀ x,chart u f.2 x≠0 → x=(fun _ => false)) : Tract F := by
  refine ⟨hF.subset (fun _ h => h.1),Or.inr (Or.inr (Or.inl ?_))⟩
  intro f hf
  exact axis_tensor u hu f.2 (haxis f hf)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- Nontractability, rather than a supplied exceptional row, supplies the
supported coefficient used by the physical cap descent. -/
theorem off_axis (u : Signature AlgebraicComplex 1) (hu : norm u≠0)
    (hnot : ¬Tract (original G)) :
    ∃ j : Fin s,∃ x : Fin (a j.val) → Bool,chart u (G j) x≠0 ∧ x≠(fun _ => false) := by
  classical
  by_contra h
  apply hnot
  apply all_axis_tract (original G) (Set.finite_range _) u hu
  intro f hf x hx
  obtain ⟨j,hj⟩ := hf.1
  subst f
  by_contra hx0
  exact h ⟨j,x,hx,hx0⟩

theorem norm_pairing (u : Signature AlgebraicComplex 1) :
    norm u=GeneralOddUnaryOrdinary.pairing u u := by
  simp [norm,GeneralOddUnaryOrdinary.pairing,Signature.connect_equality,pow_two]

variable (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
variable (hu : (result G j ho hnz).arity=1)
variable (hni : GeneralOddUnaryOrdinary.pairing
  (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote≠0)
variable (hnot : ¬Tract (original G))

include hni hnot in
/-- The selected source label, cap count and graph are all produced from the
original finite family and its real nonisotropic odd descendant. -/
theorem produced : ∃ t : Fin s,∃ m k : ℕ,0<m ∧ m+k=a t.val ∧
    ∃ V : Network AlgebraicComplex m,
      Uses V (original G) ∧ Ordinary V ∧
      EndpointSupport (chart (unary G j ho hnz hu).denote V.denote) ∧
      chart (unary G j ho hnz hu).denote V.denote (fun _ => true)≠0 ∧
      V.shape.vertices=k+1 ∧
      V.shape.edges=k*((unary G j ho hnz hu).shape.edges+1) := by
  obtain ⟨t,x,hx,hx0⟩ := off_axis G (unary G j ho hnz hu).denote
    (by rwa [norm_pairing]) hnot
  obtain ⟨m,k,hm,hmk,V,hVF,hVE,hVs,hVt,hVv,hVe⟩ :=
    descend (original G) (unary G j ho hnz hu) (unary_uses G j ho hnz hu)
      (unary_ordinary G j ho hnz hu) (a t.val) (Network.corolla (G t))
      (fun _ => ⟨t,rfl⟩) (fun e => Fin.elim0 e) x (by simpa using hx) hx0
  refine ⟨t,m,k,hm,hmk,V,hVF,hVE,hVs,hVt,?_,?_⟩
  · rw [hVv,(unary_resources G j ho hnz hu).1]
    change k*1+1=k+1
    omega
  · simpa [Network.corolla] using hVe

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicSource

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicSource
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame GeneralOddNonisotropicDescent GeneralOddUnarySource
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
variable (hu : (result G j ho hnz).arity=1)

/-- Recorded physical output, selected only after its existence is proved. -/
structure Output where
  label : Fin s
  arity : ℕ
  caps : ℕ
  positive : 0<arity
  conservation : arity+caps=a label.val
  graph : Network AlgebraicComplex arity
  uses : Uses graph (original G)
  ordinary : Ordinary graph
  support : EndpointSupport (chart (unary G j ho hnz hu).denote graph.denote)
  opposite : chart (unary G j ho hnz hu).denote graph.denote (fun _ => true)≠0
  vertices : graph.shape.vertices=caps+1
  edges : graph.shape.edges=caps*((unary G j ho hnz hu).shape.edges+1)

variable (hni : GeneralOddUnaryOrdinary.pairing
  (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote≠0)
variable (hnot : ¬Tract (original G))

def output : Output G j ho hnz hu := Classical.choice (by
  obtain ⟨t,m,k,hm,hmk,V,hVF,hVE,hVs,hVt,hVv,hVe⟩ := produced G j ho hnz hu hni hnot
  exact ⟨⟨t,m,k,hm,hmk,V,hVF,hVE,hVs,hVt,hVv,hVe⟩⟩)

theorem output_nonzero : (output G j ho hnz hu hni hnot).graph.denote≠0 := by
  intro hz
  apply (output G j ho hnz hu hni hnot).opposite
  simp [hz,chart,Signature.coordinateAction_zero]

/-- Every coefficient, including the possibly zero own-axis endpoint, is kept. -/
theorem output_entry (x : Fin (output G j ho hnz hu hni hnot).arity → Bool) :
    chart (unary G j ho hnz hu).denote (output G j ho hnz hu hni hnot).graph.denote x=
      if x=(fun _ => false) then
        chart (unary G j ho hnz hu).denote (output G j ho hnz hu hni hnot).graph.denote (fun _ => false)
      else if x=(fun _ => true) then
        chart (unary G j ho hnz hu).denote (output G j ho hnz hu hni hnot).graph.denote (fun _ => true)
      else 0 := by
  classical
  split_ifs with h0 h1
  · rw [h0]
  · rw [h1]
  · by_contra hn
    exact ((output G j ho hnz hu hni hnot).support x hn).elim h0 h1

/-- The remaining arity is bounded by the actual selected original row. -/
theorem output_bounds :
    (output G j ho hnz hu hni hnot).arity≤a (output G j ho hnz hu hni hnot).label.val ∧
    (output G j ho hnz hu hni hnot).caps<a (output G j ho hnz hu hni hnot).label.val := by
  have hp := (output G j ho hnz hu hni hnot).positive
  have hc := (output G j ho hnz hu hni hnot).conservation
  omega

/-- Boundary casts preserve every constant-word chart coefficient. -/
private theorem chart_cast_constant {m n : ℕ} (h : m=n)
    (u : Signature AlgebraicComplex 1) (N : Network AlgebraicComplex m) (b : Bool) :
    chart u (reboundary N (finCongr h)).denote (fun _ => b)=chart u N.denote (fun _ => b) := by
  cases h
  have he : (reboundary N (finCongr rfl)).denote=N.denote := by
    funext x
    rw [reboundary_denote]
    rfl
  rw [he]

/-- The arity-one result is a genuinely independent ACTUAL unary. The other
arm remains an explicit higher endpoint-support graph, not a hardness claim. -/
theorem output_classified :
    (∃ V : Network AlgebraicComplex 1,Uses V (original G) ∧ Ordinary V ∧
      GeneralOddUnaryOrdinary.determinant (unary G j ho hnz hu).denote V.denote≠0) ∨
    2≤(output G j ho hnz hu hni hnot).arity := by
  by_cases hm : (output G j ho hnz hu hni hnot).arity=1
  · left
    let V := reboundary (output G j ho hnz hu hni hnot).graph (finCongr hm)
    refine ⟨V,(output G j ho hnz hu hni hnot).uses,
      (output G j ho hnz hu hni hnot).ordinary,?_⟩
    have ht := (output G j ho hnz hu hni hnot).opposite
    rw [←chart_cast_constant hm (unary G j ho hnz hu).denote _ true] at ht
    have he : chart (unary G j ho hnz hu).denote V.denote (fun _ => true)=
        GeneralOddUnaryOrdinary.determinant (unary G j ho hnz hu).denote V.denote := by
      rw [chart_unary]
      simp only [frame,GeneralOddUnaryOrdinary.determinant]
      ring
    rwa [he] at ht
  · right
    have hp := (output G j ho hnz hu hni hnot).positive
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicSource
