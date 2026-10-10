import Holant.Proofs.Closure.ClosureMatchingMinor

/-! All contractions on one fixed original port pair of a matching tensor use
one common residual port matching. Kernel values can change matrices and the
cycle scalar, including zero, but cannot change the residual physical pairing. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMatchingResidual
open Holant Holant.Certificates.MatchingContractionClosure
variable {K P : Type} [Field K] [DecidableEq P]

structure Products (u v : P) (f : Tensor K P) : Type 1 where
  Edge : Type
  finite : Fintype Edge
  decidable : DecidableEq Edge
  ports : (Edge × Bool) ≃ Remaining u v
  matrix : Binary (K:=K) → Edge → Binary (K:=K)
  scalar : Binary (K:=K) → K
  equation : ∀ C, contractPair u v C f = @productValue K _ (Remaining u v) Edge
    finite ports (matrix C) (scalar C)

attribute [instance] Products.finite Products.decidable

/-- This is a derived common matching for all kernels, not a supplied
alignment of independently selected output factorizations. -/
theorem products_nonempty (M : Presentation K P) (u v : P) (distinct : u ≠ v) :
    Nonempty (Products u v M.tensor) := by
  classical
  let p := M.ports
  let A := M.matrix
  let e := (p.symm u).1
  let d := (p.symm v).1
  by_cases same : e = d
  · let sigma := sameMask p u
    let p' := (flipSlots sigma).trans p
    let A' := orientedFactors A sigma
    have original : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar sigma
    obtain ⟨hu,hv⟩ := same_selected_ports p u v distinct same
    change p' (e,false) = u at hu
    change p' (e,true) = v at hv
    have localResult : Nonempty (Products (p' (e,false)) (p' (e,true)) (productValue p' A' M.scalar)) := by
      refine ⟨{
        Edge := OtherEdges e
        finite := inferInstance
        decidable := inferInstance
        ports := deletePorts p' e
        matrix := fun _ i => A' i.val
        scalar := fun C => trace (A' e) C * M.scalar
        equation := ?_ }⟩
      intro C
      exact contract_matched p' A' M.scalar e C
    simpa only [hu,hv,original] using localResult
  · let sigma := crossMask p u v
    let p' := (flipSlots sigma).trans p
    let A' := orientedFactors A sigma
    have original : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar sigma
    obtain ⟨hu,hv⟩ := cross_selected_ports p u v same
    change p' (e,true) = u at hu
    change p' (d,false) = v at hv
    have localResult : Nonempty (Products (p' (e,true)) (p' (d,false)) (productValue p' A' M.scalar)) := by
      refine ⟨{
        Edge := OtherEdges d
        finite := inferInstance
        decidable := inferInstance
        ports := splicePorts p' e d
        matrix := fun C => spliceFactors C A' e d
        scalar := fun _ => M.scalar
        equation := ?_ }⟩
      intro C
      exact contract_cross p' A' M.scalar e d same C
    simpa only [hu,hv,original] using localResult

def products (M : Presentation K P) (u v : P) (distinct : u ≠ v) : Products u v M.tensor :=
  Classical.choice (products_nonempty M u v distinct)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMatchingResidual
end
