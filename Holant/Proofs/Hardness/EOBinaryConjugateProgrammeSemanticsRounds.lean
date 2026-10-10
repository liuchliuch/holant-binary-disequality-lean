import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeSemanticsScan

/-! Exact outer rounds and denominator safety for the collision-aware controller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
set_option maxRecDepth 32768
set_option Elab.async false
variable {L : Type} [Field L]

/-- The actual ten-field state at the beginning of a desired-root pass. -/
def ready (roots : List (L×L)) (moments : List L) (pending : List (L×L))
    (num div : L) (fuel : ℕ) : S.State L :=
  ⟨roots,moments,pending,roots,moments,(pending.getD 0 (0,0)).1,0,num,div,fuel⟩

def factor (roots : List (L×L)) (p : L×L) : L :=
  A.denominator (roots.map Prod.fst) p.1*(A.multiplicity (roots.map Prod.fst) p.1 : L)

def weighted (roots : List (L×L)) (values : ℕ→L) (p : L×L) : L :=
  p.2*A.numerator (roots.map Prod.fst) p.1 values

def contribution (roots : List (L×L)) (values : ℕ→L) (p : L×L) : L :=
  weighted roots values p/factor roots p

/-- A pass scans every original root once and then cross-multiplies the accumulator. -/
theorem round_exact (roots : List (L×L)) (values : ℕ→L)
    (p : L×L) (pending : List (L×L)) (hp : p∈roots) (num div : L) (fuel : ℕ) :
    S.step^[roots.length+1] (ready roots (V.table roots.length values) (p::pending) num div fuel)=
      ready roots (V.table roots.length values) pending
        (num*factor roots p+weighted roots values p*div) (div*factor roots p) fuel := by
  have hmem : p.1∈roots.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
  have hlen := EOBinaryConjugateProgrammeFilter.unwanted_length (roots.map Prod.fst) p.1 hmem
  simp only [List.length_map] at hlen
  let u := (A.unwanted (roots.map Prod.fst) p.1).length
  have hq : u+(roots.length-u)=roots.length := by dsimp [u]; omega
  have hn : 0<roots.length-u := by dsimp [u]; omega
  have hs := scan_exact roots roots (V.table roots.length values) p pending values
    (roots.length-u) p.1 0 num div fuel
  rw [hq] at hs
  rw [Function.iterate_succ_apply']
  change S.step (S.step^[roots.length]
    (⟨roots,V.table roots.length values,p::pending,roots,V.table roots.length values,
      p.1,0,num,div,fuel⟩ : S.State L)) = _
  rw [hs]
  simp [S.step,EOBinaryConjugateProgrammeState.advance,S.desired,
    EOBinaryConjugateProgrammeState.nextDesired,ready,factor,weighted,A.denominator,
    A.numerator]
  exact Or.inl (Or.inl (table_head _ _ hn))

variable [CharZero L]

/-- Positivity of the counted copies and a nonzero desired root justify division. -/
theorem factor_ne_zero (roots : List (L×L)) (p : L×L) (hp : p∈roots) (hz : p.1≠0) :
    factor roots p≠0 := by
  apply mul_ne_zero (EOBinaryConjugateProgrammeFilter.denominator_ne_zero _ _ hz)
  apply Nat.cast_ne_zero.mpr
  exact Nat.ne_of_gt (EOBinaryConjugateProgrammeFilter.multiplicity_pos _ _
    (List.mem_map.mpr ⟨p,hp,rfl⟩))

omit [CharZero L] in
/-- No division takes place during the loop; this identity validates its stored fraction. -/
theorem accumulator_add (num div a b : L) (hd : div≠0) (hb : b≠0) :
    (num*b+a*div)/(div*b)=num/div+a/b := by
  field_simp [hd,hb]

/-- The full outer loop terminates with the exact sum and a nonzero divisor. -/
theorem outer_exact (roots : List (L×L)) (values : ℕ→L)
    (hr : ∀p∈roots,p.1≠0) (pending : List (L×L))
    (hp : ∀p∈pending,p∈roots) (num div : L) (hd : div≠0) (fuel : ℕ) :
    let final := S.step^[pending.length*(roots.length+1)]
      (ready roots (V.table roots.length values) pending num div fuel)
    final.pending=[] ∧ final.divisor≠0 ∧
      final.numerator/final.divisor=num/div+(pending.map (contribution roots values)).sum := by
  induction pending generalizing num div with
  | nil => simpa [ready] using hd
  | cons p ps ih =>
    have hpr := hp p (by simp)
    have hb := factor_ne_zero roots p hpr (hr p hpr)
    have htail : ∀p∈ps,p∈roots := fun p h=>hp p (List.mem_cons_of_mem _ h)
    have hrest := ih htail (num*factor roots p+weighted roots values p*div)
      (div*factor roots p) (mul_ne_zero hd hb)
    dsimp only at hrest ⊢
    rw [List.length_cons,Nat.add_mul,one_mul,Function.iterate_add_apply,round_exact roots values p ps hpr]
    refine ⟨hrest.1,hrest.2.1,?_⟩
    rw [hrest.2.2,accumulator_add _ _ _ _ hd hb]
    simp [contribution,add_assoc]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeSemantics
