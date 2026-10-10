import Holant.Proofs.Closure.ClosureStableFactorLines
import Holant.Proofs.Closure.ClosureStableFactorPorts
import Holant.Proofs.Closure.ClosureStableFactorDescent
import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrentFamily
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! All-arity ancestor reconstruction from the actual CURRENT native-M deck.
The common matching and pairwise factor-line bound are derived by the queue
factory. No FourProducts, selected nonzero grid or whole-family certificate is
an input. Zero cards lie in the same exact fixed-factor linear subspace. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open ClosureCompatibleAlignment

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)
variable (anchor : ClosureCompatibleAlignment.Sample G P torsion N f order)

theorem current_fixed_edge (large : 2 ≤ r) :
    ∃ edge : Fin (r+1), ∀ i : ClosureCompatibleAlignment.Sample G P torsion N f order,
      ProjectivelyEqual (familyTables G P torsion N f order stable anchor i edge)
        (familyTables G P torsion N f order stable anchor anchor edge) := by
  let : NeZero r := ⟨by omega⟩
  exact projective_fixed_coordinate (familyTables G P torsion N f order stable anchor) anchor
    (family_distance_le_one G P torsion N f order stable anchor large)

def factorResidualOrder (edge : Fin (r+1)) : Equiv.Perm (Fin (2*r+2)) :=
  pairOrder (familyPorts G P torsion N f order stable anchor (edge,false))
    (familyPorts G P torsion N f order stable anchor (edge,true))

def normalizedAncestor (edge : Fin (r+1)) : Signature Scalar (2*r+4) :=
  Tensor.reindex (liftResidual (factorResidualOrder G P torsion N f order stable anchor edge)).symm
    (Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f))

theorem factor_order_first (edge : Fin (r+1)) :
    factorResidualOrder G P torsion N f order stable anchor edge 0=
      familyPorts G P torsion N f order stable anchor (edge,false) := by
  apply pairOrder_first
  intro equal
  have pairEqual := (familyPorts G P torsion N f order stable anchor).injective equal
  have bitEqual := congrArg Prod.snd pairEqual
  cases bitEqual

theorem factor_order_second (edge : Fin (r+1)) :
    factorResidualOrder G P torsion N f order stable anchor edge 1=
      familyPorts G P torsion N f order stable anchor (edge,true) := pairOrder_second _ _

theorem every_sample_fixed_factor (large : 2 ≤ r) (edge : Fin (r+1))
    (fixed : ∀ i : ClosureCompatibleAlignment.Sample G P torsion N f order,
      ProjectivelyEqual (familyTables G P torsion N f order stable anchor i edge)
        (familyTables G P torsion N f order stable anchor anchor edge))
    (sector : Bool) (t : {t : Scalar // Roots N.m t}) :
    ∃ R : Signature Scalar (2*r), ∀ b c x,
      close sector t.val (normalizedAncestor G P torsion N f order stable anchor edge) (pair b c x)=
        familyTables G P torsion N f order stable anchor anchor edge b c * R x := by
  classical
  let u := factorResidualOrder G P torsion N f order stable anchor edge
  have transport : close sector t.val (normalizedAncestor G P torsion N f order stable anchor edge)=
      Tensor.reindex u.symm (normalizedCurrentCard G P torsion N f order sector t) :=
    close_liftResidual u _ sector t.val
  by_cases zero : normalizedCurrentCard G P torsion N f order sector t=0
  · refine ⟨0,?_⟩
    intro b c x
    rw [congrFun transport (pair b c x),zero]
    simp [Tensor.reindex]
  · let i : ClosureCompatibleAlignment.Sample G P torsion N f order := ⟨(sector,t),zero⟩
    let ports := (familyPorts G P torsion N f order stable anchor).trans u.symm
    have first : ports (edge,false)=0 := by
      change u.symm (familyPorts G P torsion N f order stable anchor (edge,false))=0
      rw [←factor_order_first G P torsion N f order stable anchor edge]
      exact u.symm_apply_apply 0
    have second : ports (edge,true)=1 := by
      change u.symm (familyPorts G P torsion N f order stable anchor (edge,true))=1
      rw [←factor_order_second G P torsion N f order stable anchor edge]
      exact u.symm_apply_apply 1
    obtain ⟨R,extraction⟩ := product_fixed_factor ports
      (familyTables G P torsion N f order stable anchor i)
      (familyCoefficient G P torsion N f order stable i) edge first second _ (fixed i)
    refine ⟨R,?_⟩
    intro b c x
    rw [congrFun transport (pair b c x)]
    change normalizedCurrentCard G P torsion N f order i.val.1 i.val.2
      (fun j => pair b c x (u.symm j)) = _
    rw [family_card_equation G P torsion N f order stable anchor large i]
    exact extraction b c x

theorem current_ambient_split (large : 2 ≤ r) :
    ∃ edge : Fin (r+1), ∃ R : Signature Scalar (2*r+2),
      ∃ split : ProperSplit
        (⟨2*r+4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f⟩ : AnySignature Scalar)
        ⟨2,kernelSignature (familyTables G P torsion N f order stable anchor anchor edge)⟩ ⟨2*r+2,R⟩,
      split.ports=(factorPorts (2*r)).trans
        ((liftResidual (factorResidualOrder G P torsion N f order stable anchor edge)).trans order) ∧
        split.scale=1 := by
  classical
  obtain ⟨edge,fixed⟩ := current_fixed_edge G P torsion N f order stable anchor large
  let u := factorResidualOrder G P torsion N f order stable anchor edge
  let original := (liftResidual u).trans order
  let t₀ : {t : Scalar // Roots N.m t} := ⟨1,Roots.one N.m⟩
  obtain ⟨t₁,square⟩ := root_square_avoids N.range 1
  have different : t₀.val≠t₁.val := by
    intro same
    apply square
    simp only [←same,t₀,one_pow]
  let t : Bool → {t : Scalar // Roots N.m t} := fun b => if b then t₁ else t₀
  have factors (i : Bool × Bool) : ∃ R : Signature Scalar (2*r), ∀ b c x,
      close i.1 (phase t₀.val t₁.val i)
        (normalizedAncestor G P torsion N f order stable anchor edge) (pair b c x)=
          familyTables G P torsion N f order stable anchor anchor edge b c * R x := by
    cases i with
    | mk gamma bit =>
      cases bit
      · simpa only [phase,reduceCtorEq,ite_false] using every_sample_fixed_factor G P torsion N f order stable anchor
          large edge fixed gamma t₀
      · simpa only [phase,ite_true] using every_sample_fixed_factor G P torsion N f order stable anchor
          large edge fixed gamma t₁
  choose H equations using factors
  let R := inverseSlices t₀.val t₁.val H
  have normalizedFactor : normalizedAncestor G P torsion N f order stable anchor edge =
      Tensor.reindex (factorPorts (2*r)) (Tensor.tensor
        (kernelSignature (familyTables G P torsion N f order stable anchor anchor edge)) R) :=
    tensor_factor_of_slices _ _ _ (four_card_inversion t₀.val t₁.val different _ _ H equations)
  have exactOriginal : Tensor.reindex original
      (normalizedAncestor G P torsion N f order stable anchor edge)=
        RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f := by
    funext x
    simp only [normalizedAncestor,Tensor.reindex,original,Equiv.trans_apply]
    congr 1
    funext j
    simp only [u,Equiv.apply_symm_apply]
  have equation : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f =
      Tensor.reindex ((factorPorts (2*r)).trans original) (Tensor.tensor
        (kernelSignature (familyTables G P torsion N f order stable anchor anchor edge)) R) := by
    rw [←exactOriginal,normalizedFactor]
    rfl
  exact ⟨edge,R,ClosureTensorPrimeFactors.splitOfTensor _ _ _
    ((factorPorts (2*r)).trans original) (by omega) (by omega) equation,rfl,rfl⟩

def anchorOriginalBinary (edge : Fin (r+1)) : Matrix Bool Bool (OI.K G) :=
  (selectedSample G P torsion N f order stable anchor).native.matrix
    ((finCongr (selectedSample G P torsion N f order stable anchor).edgeCount).symm edge)

def anchorOriginalTable (edge : Fin (r+1)) : Signature (OI.K G) 2 :=
  fun x => anchorOriginalBinary G P torsion N f order stable anchor edge (x 0) (x 1)

theorem anchor_original_exact (edge : Fin (r+1)) :
    Matrix.map (anchorOriginalBinary G P torsion N f order stable anchor edge)
      (ClosureSourceRows.embedding G)=familyTables G P torsion N f order stable anchor anchor edge :=
  (familyTables_anchor_original G P torsion N f order stable anchor edge).symm

theorem anchor_original_nonzero (edge : Fin (r+1)) :
    anchorOriginalTable G P torsion N f order stable anchor edge≠0 := by
  have nonsingular := groupM_det_nonzero (by have := N.range; omega)
    (familyTables_member G P torsion N f order stable anchor anchor edge)
  obtain ⟨b,c,live⟩ := Holant.Certificates.MatchingContractionClosure.nonsingular_has_entry _ nonsingular
  intro zero
  have sourceZero : anchorOriginalBinary G P torsion N f order stable anchor edge b c=0 :=
    congrFun zero (Fin.cons b (Fin.cons c Fin.elim0))
  apply live
  rw [←anchor_original_exact G P torsion N f order stable anchor edge]
  simp only [Matrix.map_apply,sourceZero,map_zero]

/-- Original-field coefficient descent retains the actual saved anchor
binary, the exact original ordered partition, and unit multiplier one. -/
theorem current_original_split (large : 2 ≤ r) :
    ∃ edge : Fin (r+1), ∃ R : Signature (OI.K G) (2*r+2),
      ∃ split : ProperSplit (⟨2*r+4,f⟩ : AnySignature (OI.K G))
        ⟨2,anchorOriginalTable G P torsion N f order stable anchor edge⟩ ⟨2*r+2,R⟩,
      split.ports=(factorPorts (2*r)).trans
        ((liftResidual (factorResidualOrder G P torsion N f order stable anchor edge)).trans order) ∧
        split.scale=1 := by
  obtain ⟨edge,R,s,ports,scale⟩ := current_ambient_split G P torsion N f order stable anchor large
  let B := anchorOriginalTable G P torsion N f order stable anchor edge
  let φ := ClosureSourceRows.embedding G
  have mappedLeft : (fun x => φ (B x))=
      kernelSignature (familyTables G P torsion N f order stable anchor anchor edge) := by
    funext x
    exact congrFun (congrFun (anchor_original_exact G P torsion N f order stable anchor edge) (x 0)) (x 1)
  let mapped : ProperSplit (mapSignature φ (⟨2*r+4,f⟩ : AnySignature (OI.K G)))
      (mapSignature φ (⟨2,B⟩ : AnySignature (OI.K G))) ⟨2*r+2,R⟩ := {
    left_pos := s.left_pos
    right_pos := s.right_pos
    ports := s.ports
    scale := s.scale
    equation := by
      funext x
      have h := congrFun s.equation x
      change φ (f x)=(s.scale : Scalar)*
        ((fun y => φ (B y)) (fun i => x (s.ports (.inl i))) * R (fun i => x (s.ports (.inr i))))
      rw [mappedLeft]
      exact h }
  obtain ⟨right,result,exactPorts,exactScale⟩ := known_left_descends φ f B
    (anchor_original_nonzero G P torsion N f order stable anchor edge) R mapped
  exact ⟨edge,right,result,exactPorts.trans ports,exactScale⟩

/-- Closed nonzero-source constructor. The actual anchor is selected
internally; the returned original-field factor is its literal saved matrix,
with the original 2+(n−2) partition and unit multiplier one. -/
theorem current_original_split_of_nonzero (nonzero : f≠0) (large : 2 ≤ r) :
    let chosen := canonicalAnchor G P torsion N f order nonzero
    ∃ edge : Fin (r+1), ∃ R : Signature (OI.K G) (2*r+2),
      ∃ split : ProperSplit (⟨2*r+4,f⟩ : AnySignature (OI.K G))
        ⟨2,anchorOriginalTable G P torsion N f order stable chosen edge⟩ ⟨2*r+2,R⟩,
      split.ports=(factorPorts (2*r)).trans
        ((liftResidual (factorResidualOrder G P torsion N f order stable chosen edge)).trans order) ∧
        split.scale=1 := by
  exact current_original_split G P torsion N f order stable
    (canonicalAnchor G P torsion N f order nonzero) large

include P torsion N order stable

/-- The anchor is constructed internally from the actual nonzero ancestor;
the common matching, line bound and fixed edge are all derived from CURRENT
native-M stability. Only the real stable source deck is an input. -/
theorem current_nativeM_not_prime (large : 2 ≤ r) :
    ¬Prime (⟨2*r+4,f⟩ : AnySignature (OI.K G)) := by
  intro prime
  let chosen := canonicalAnchor G P torsion N f order prime.1
  obtain ⟨edge,R,split,_,_⟩ := current_original_split_of_nonzero G P torsion N f order stable prime.1 large
  exact prime.2 ⟨⟨2,anchorOriginalTable G P torsion N f order stable chosen edge⟩,⟨2*r+2,R⟩,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
