import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinNonrealDescent

/-! Factor saturation selects an actual retained non-real prime. Literal
no-unary/no-odd guards and the standard complete binary group put it in the
even nonbinary domain, where the exact raw-card descent gives an original-G
quaternary source. The all-real whole-family alternative is left explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardNonrealSource
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Pauli.ProjectiveDetermination
namespace D
export GlobalCloseCompletionKleinNonrealDescent (phi complexTensor arity arity_eq Output from_retained nonreal_not_matching)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem realLine_factorTree {L : Type*} [Field L] (phi : L→+*ℂ)
    {f : AnySignature L} (tree : FactorTree f)
    (leaves : ∀g∈tree.leaves,IsRealLine (RingHomRealization.mapSignature phi g.2)) :
    IsRealLine (RingHomRealization.mapSignature phi f.2) := by
  induction tree with
  | leaf f prime => exact leaves f (by simp [FactorTree.leaves])
  | @split f a b split left right ihl ihr =>
    obtain ⟨c,hc,l,hl⟩ := ihl (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inl hg)))
    obtain ⟨d,hd,r,hr⟩ := ihr (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inr hg)))
    refine ⟨phi (split.scale : L)*c*d,mul_ne_zero (mul_ne_zero ((map_ne_zero phi).mpr split.scale.ne_zero) hc) hd,
      (fun x=>l (fun i=>x (split.ports (.inl i)))*r (fun i=>x (split.ports (.inr i)))),?_⟩
    funext x
    change phi (f.2 x)=_
    rw [split.equation,map_mul,map_mul]
    have hleft := congrFun hl (fun i=>x (split.ports (.inl i)))
    have hright := congrFun hr (fun i=>x (split.ports (.inr i)))
    change phi (a.2 _)=_ at hleft
    change phi (b.2 _)=_ at hright
    rw [hleft,hright,Complex.ofReal_mul]
    ring

private theorem nonreal_leaf {L : Type*} [Field L] (phi : L→+*ℂ)
    {f : AnySignature L} (tree : FactorTree f)
    (nonreal : ¬IsRealLine (RingHomRealization.mapSignature phi f.2)) :
    ∃g∈tree.leaves,¬IsRealLine (RingHomRealization.mapSignature phi g.2) := by
  classical
  by_contra h
  push Not at h
  exact nonreal (realLine_factorTree phi tree h)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)
variable (noUnary : ¬RetainedUnary P.family)
variable (noOdd : ∀g∈P.family,Prime g→3≤g.1→Even g.1)

include cardinal noncyclic standard noUnary in
theorem nonreal_prime_nonbinary (g : AnySignature (OI.K G)) (retained : g∈P.family)
    (prime : Prime g) (nonreal : ¬IsRealLine (D.complexTensor G g.2)) : 3≤g.1 := by
  have positive : 0<g.1 := by
    obtain ⟨j,hj⟩ := retained
    rw [←hj]
    exact P.positive j
  by_contra small
  have cases : g.1=1 ∨ g.1=2 := by omega
  rcases g with ⟨m,f⟩
  rcases cases with rfl|rfl
  · exact noUnary ⟨f,retained,prime.1⟩
  · apply D.nonreal_not_matching G P torsion cardinal noncyclic standard f nonreal
    apply FactorTree.matchingOrZero (.leaf ⟨2,f⟩ prime) P.family
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact eq.symm ▸ retained
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact congrArg Sigma.fst eq

include cardinal noncyclic standard noUnary noOdd in
theorem retained_nonreal_source (i : Fin P.count)
    (nonreal : ¬IsRealLine (D.complexTensor G (P.table i))) : Nonempty (D.Output G P) := by
  obtain ⟨g,hg,bad⟩ := nonreal_leaf (D.phi G) (P.trees i) nonreal
  have retained := P.leavesRetained i g hg
  have prime := (P.trees i).leaves_prime g hg
  have nonbinary := nonreal_prime_nonbinary G P torsion cardinal noncyclic standard noUnary g retained prime bad
  have even := noOdd g retained prime nonbinary
  rcases g with ⟨m,f⟩
  obtain ⟨k,hk⟩ := even
  change m=k+k at hk
  change 3≤m at nonbinary
  have lower : 2≤k := by omega
  have size : m=D.arity (k-2) := by rw [D.arity_eq];omega
  clear hk
  subst m
  exact ⟨D.from_retained G P torsion cardinal noncyclic standard (k-2) f retained bad⟩

def AllReal : Prop := ∀i : Fin P.count,IsRealLine (D.complexTensor G (P.table i))

include cardinal noncyclic standard noUnary noOdd in
theorem all_real_or_quaternary : AllReal G P ∨ Nonempty (D.Output G P) := by
  classical
  by_cases all : AllReal G P
  · exact Or.inl all
  · rw [AllReal] at all
    push Not at all
    obtain ⟨i,nonreal⟩ := all
    exact Or.inr (retained_nonreal_source G P torsion cardinal noncyclic standard noUnary noOdd i nonreal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardNonrealSource
end
