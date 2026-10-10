import Holant.Proofs.Closure.FrontierNativeClosure
import Holant.Proofs.Closure.ClosureMarkedSourceRouting
import Holant.Tractable.SymmetricBinaryPullback.Product

/-! Current binary closure at the actual marked basis. Every retained binary
prime is an actual nonsingular original-field binary, so the constructed
complete-group spectra give product membership for every saved occurrence.
The same basis also puts the native edge in the product class. No binary
membership, edge certificate, alternate basis, or whole-family closure is a
caller hypothesis. Higher even leaves remain a separate mathematical task. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentBinaryClosure
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation CurrentFrontierClosure

/-- Monomial support supplies an actual product formula, with arbitrary
nonzero weights retained rather than rounded to phases. -/
theorem product_of_marked_monomial {B : Mat} (h : IsMonomial B) :
    Product (kernelSignature B) := by
  obtain ⟨p,w,_hw,rfl⟩ := h
  apply SymmetricBinaryPullback.product_of_monomial
  cases p
  · exact Or.inl ⟨by simp [monomial],by simp [monomial]⟩
  · exact Or.inr ⟨by simp [monomial],by simp [monomial]⟩

theorem hadamard_edge_monomial :
    IsMonomial (sectorEdge ClosureMarkedCyclic.basis) := by
  rw [ClosureMarkedCyclic.same_edge]
  exact (diagonal_isMonomial one_ne_zero (neg_ne_zero.mpr one_ne_zero)).scale (by norm_num)

theorem hadamard_inverse_edge_monomial :
    IsMonomial (sectorEdgeInverse ClosureMarkedCyclic.basis) := by
  have he := edgeInverseA_eta (s:=1) (eta:=1) one_ne_zero (by simp : (1:Scalar)^2 = 1⁻¹)
  change sectorEdgeInverse ClosureMarkedCyclic.basis = _ at he
  rw [he]
  exact (diagonal_isMonomial one_ne_zero (neg_ne_zero.mpr one_ne_zero)).scale (by norm_num)

section OriginalField
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)

/-- The cyclic model supplies an exact source-field ratio. The actual table
uses that ratio and the same Hadamard inverse edge, hence is monomial too. -/
theorem cyclic_binary_monomial
    (N : ClosureMarkedCyclic.NativeCyclic (ClosureMarkedDihedral.Source.group phi F torsion))
    (B : Binary (K:=L)) (actual : ActualNonsingular F B) :
    IsMonomial (transport ClosureMarkedCyclic.basis (Matrix.map B phi)) := by
  obtain ⟨c,t,hc,ht,he⟩ := ClosureMarkedCyclic.Source.actual_source_ratios phi F torsion N B actual
  have ht0 : t ≠ 0 := by
    intro hz
    have hm : N.m ≠ 0 := by have := N.range; omega
    rw [hz,zero_pow hm] at ht
    exact zero_ne_one ht
  have htransfer : sectorTransfer ClosureMarkedCyclic.basis (Matrix.map B phi) =
      scale (phi c) (R (phi t)) := by
    rw [← ClosureMarkedCyclic.Source.sourceTransfer_map,he]
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.map_apply,ClosureMarkedCyclic.Source.rotation,scale,R,diagonalKernel]
  rw [transport_eq_transfer,htransfer]
  exact ((diagonal_isMonomial one_ne_zero ((map_ne_zero phi).mpr ht0)).scale
    ((map_ne_zero phi).mpr hc)).mul hadamard_inverse_edge_monomial

/-- Every basis actually exposed by the native marking has a product-class
native edge, with its exact multiplier and with that very same U. The small
and Platonic branches expose no such basis and remain outside this theorem. -/
theorem marking_edge_monomial
    (equality : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (M : ClosureMarkedSourceRouting.Marking phi F torsion)
    (U : InvertibleKernel) (selected : M.basis = some U) :
    IsMonomial (sectorEdge U) := by
  cases M with
  | smallTwo => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | smallFour => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | platonic => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | cyclic N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact hadamard_edge_monomial
  | monomial N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact N.parameters.edge_isMonomial
  | bilinear N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact N.parameters.edge_isMonomial
  | unshifted nativeZ N sourceY =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact hadamard_edge_monomial
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact (reflection.parameters equality axis notTwo notFour noZ).edge_isMonomial

/-- Actual source spectra, including cyclic, unshifted and shifted sectors,
close every ordered nonsingular binary at the selected common basis. -/
theorem marking_binary_monomial
    (equality : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (M : ClosureMarkedSourceRouting.Marking phi F torsion)
    (U : InvertibleKernel) (selected : M.basis = some U)
    (B : Binary (K:=L)) (actual : ActualNonsingular F B) :
    IsMonomial (transport U (Matrix.map B phi)) := by
  cases M with
  | smallTwo => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | smallFour => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | platonic => simp [ClosureMarkedSourceRouting.Marking.basis] at selected
  | cyclic N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact cyclic_binary_monomial phi F torsion N B actual
  | monomial N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact N.parameters.actual_isMonomial _ _
        (ClosureMarkedDihedral.Source.actual_sector_transfer phi F torsion N B actual)
        (ProjectivelyEqual.refl _)
  | bilinear N =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact ClosureMarkedDihedralB.Source.actual_transformed_monomial phi F torsion N B actual
  | unshifted nativeZ N sourceY =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      rw [transport_eq_transfer]
      exact (groupM_isMonomial (by have := N.selected.range; omega)
        (ClosureMarkedDihedralA0.Source.actual_sector_spectrum phi F torsion N B actual)).mul
        hadamard_inverse_edge_monomial
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      simp only [ClosureMarkedSourceRouting.Marking.basis,Option.some.injEq] at selected
      subst U
      exact (reflection.parameters equality axis notTwo notFour noZ).actual_isMonomial _ _
        (reflection.actual_sector_spectrum axis notTwo notFour B actual)
        (ProjectivelyEqual.refl _)
end OriginalField

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
abbrev embedding : OI.K G →+* AlgebraicComplex :=
  (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom

/-- Retention and primality, not an assumed binary closure theorem, establish
membership for every actual saved binary occurrence at this same basis. -/
theorem current_binary_product (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U)
    (o : CurrentOccurrences.Id G P) (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 2) :
    leafPredicate G productClass U (CurrentOccurrences.savedLeaf G P o).1 := by
  have retained := CurrentOccurrences.savedLeaf_retained G P o
  have prime := CurrentOccurrences.savedLeaf_prime G P o
  generalize hleaf : (CurrentOccurrences.savedLeaf G P o).1 = f at *
  rcases f with ⟨n,f⟩
  dsimp only at arity
  subst n
  have h := product_of_marked_monomial (marking_binary_monomial (embedding G) P.family torsion
    P.equality M U selected (binaryMatrix f) (retained_binary_prime_actual P.family f retained prime))
  have hm : kernelSignature (Matrix.map (binaryMatrix f) (embedding G)) = (embed G ⟨2,f⟩).2 := by
    funext x
    change embedding G (f ![x 0,x 1]) = embedding G (f x)
    congr 2
    funext i
    fin_cases i <;> rfl
  change Product (U.symm.action (embed G ⟨2,f⟩).2)
  rw [← hm,transport_signature]
  exact h

/-- Simultaneous mandatory edge membership for current_binary_product. -/
theorem current_native_edge_product (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U) :
    (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ productClass :=
  product_of_marked_monomial (marking_edge_monomial (embedding G) P.family torsion
    P.equality M U selected)

/-- Every unary belongs to the product class after any fixed basis action;
this includes zero unaries and needs no no-unary shortcut. -/
theorem unary_product (f : Signature AlgebraicComplex 1) : Product f := by
  have h := product_unary (0 : Fin 1) (fun b => f (fun _ => b))
  convert h using 1
  funext x
  congr 1
  funext i
  fin_cases i
  rfl

theorem current_unary_product (P : Palette G) (U : InvertibleKernel)
    (o : CurrentOccurrences.Id G P) (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 1) :
    leafPredicate G productClass U (CurrentOccurrences.savedLeaf G P o).1 := by
  generalize hleaf : (CurrentOccurrences.savedLeaf G P o).1 = f at *
  rcases f with ⟨n,f⟩
  dsimp only at arity
  subst n
  exact unary_product (U.symm.action (embed G ⟨1,f⟩).2)

/-- All small saved occurrences share one basis, including duplicate labels
or repeated leaves with distinct stored addresses. -/
structure SmallCurrentProducts (P : Palette G) (U : InvertibleKernel) : Prop where
  edge : (⟨2,kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
    AnySignature AlgebraicComplex) ∈ productClass
  leaves : ∀ o : CurrentOccurrences.Id G P, (CurrentOccurrences.savedLeaf G P o).1.1 ≤ 2 →
    leafPredicate G productClass U (CurrentOccurrences.savedLeaf G P o).1

theorem small_current_products (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U) : SmallCurrentProducts G P U := by
  refine ⟨current_native_edge_product G P torsion M U selected,?_⟩
  intro o small
  have positive := CurrentOccurrences.savedLeaf_positive G P o
  have casesArity : (CurrentOccurrences.savedLeaf G P o).1.1 = 1 ∨
      (CurrentOccurrences.savedLeaf G P o).1.1 = 2 := by omega
  rcases casesArity with unary | binary
  · exact current_unary_product G P U o unary
  · exact current_binary_product G P torsion M U selected o binary

/-- This subfamily is read from the actual saved current occurrence IDs. -/
def smallCurrentFamily (P : Palette G) : SignatureFamily AlgebraicComplex :=
  Set.range (fun o : {o : CurrentOccurrences.Id G P //
    (CurrentOccurrences.savedLeaf G P o).1.1 ≤ 2} => embed G (CurrentOccurrences.savedLeaf G P o.val).1)

theorem small_current_same_basis (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U) :
    IsCommonKBasis productClass (smallCurrentFamily G P) U := by
  have h := small_current_products G P torsion M U selected
  refine ⟨h.edge,?_⟩
  rintro _ ⟨⟨o,small⟩,rfl⟩
  exact h.leaves o small

theorem small_current_common_presentation (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U) :
    CommonKPresentationInKCoordinates productClass (smallCurrentFamily G P) :=
  ⟨Set.finite_range _,U,small_current_same_basis G P torsion M U selected⟩

/-- A closed producer on the actual current palette: marking, basis selection,
native-edge membership and all small saved-leaf proofs are constructed here.
The no-basis alternatives remain visible in marking.basis. -/
structure Output (P : Palette G) (torsion : ResidualTorsion P.family) : Type 1 where
  marking : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion
  markingIdentity : marking = ClosureMarkedSourceRouting.produce (embedding G) P.family torsion P.equality
  small : ∀ U : InvertibleKernel, marking.basis = some U → SmallCurrentProducts G P U

def produce (P : Palette G) (torsion : ResidualTorsion P.family) : Output G P torsion :=
  let M := ClosureMarkedSourceRouting.produce (embedding G) P.family torsion P.equality
  ⟨M,rfl,fun U selected => small_current_products G P torsion M U selected⟩

/-- In a genuine all-even stable output, the precise remaining product-class
local theorem is only the higher-even part. The binary and native-edge proofs
are already closed above; this equivalence does not assert that the remaining
higher-even theorem holds. -/
theorem local_product_iff_even (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (embedding G) P.family torsion)
    (U : InvertibleKernel) (selected : M.basis = some U)
    (noOdd : ∀ f ∈ P.family, Prime f → 3 ≤ f.1 → Even f.1) :
    LocalCurrentTheorems G P (leafPredicate G productClass U) ↔
      ∀ o : CurrentOccurrences.Id G P, CurrentOccurrences.Domain G P o →
        4 ≤ (CurrentOccurrences.savedLeaf G P o).1.1 →
        Even (CurrentOccurrences.savedLeaf G P o).1.1 →
        leafPredicate G productClass U (CurrentOccurrences.savedLeaf G P o).1 := by
  constructor
  · exact fun h => h.evenNonbinary
  · intro even
    refine ⟨fun o _ arity => current_unary_product G P U o arity,
      fun o _ arity => current_binary_product G P torsion M U selected o arity,?_,even⟩
    intro o _ nonbinary odd
    exact False.elim (no_current_odd G P noOdd o nonbinary odd)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentBinaryClosure
end
