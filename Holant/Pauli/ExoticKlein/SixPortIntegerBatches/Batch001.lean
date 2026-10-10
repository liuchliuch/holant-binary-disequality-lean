import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortOrbitWitness

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def irep0016State : DirectionTriple := ![none,some (directionEquiv 0),some (directionEquiv 10)]

def irep0016Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(2),(0)⟩ : GZ)),(16,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-4)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(4)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-4)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0016Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0016Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0016Node0Reductions irep0016Node0Children

theorem irep0016_cached_checked :
    irep0016Node0.check (cachedIntegerProblem irep0016State) (integerInitialRows irep0016State) = true := by
  decide +kernel

theorem irep0016_checked :
    irep0016Node0.check (integerProblem irep0016State) (integerInitialRows irep0016State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0016_cached_checked

theorem irep0016_solved : Solved irep0016State :=
  solved_of_integer_certificate irep0016State irep0016Node0 irep0016_checked

theorem irep0016_representative : Solved (stateEquiv (representativeCode 16)) := by
  have he : stateEquiv (representativeCode 16) = irep0016State := by decide +kernel
  rw [he]
  exact irep0016_solved

def irep0017State : DirectionTriple := ![none,some (directionEquiv 0),some (directionEquiv 16)]

def irep0017Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1),(6,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0017Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0017Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0017Node0Reductions irep0017Node0Children

theorem irep0017_cached_checked :
    irep0017Node0.check (cachedIntegerProblem irep0017State) (integerInitialRows irep0017State) = true := by
  decide +kernel

theorem irep0017_checked :
    irep0017Node0.check (integerProblem irep0017State) (integerInitialRows irep0017State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0017_cached_checked

theorem irep0017_solved : Solved irep0017State :=
  solved_of_integer_certificate irep0017State irep0017Node0 irep0017_checked

theorem irep0017_representative : Solved (stateEquiv (representativeCode 17)) := by
  have he : stateEquiv (representativeCode 17) = irep0017State := by decide +kernel
  rw [he]
  exact irep0017_solved

def irep0018State : DirectionTriple := ![none,some (directionEquiv 0),some (directionEquiv 17)]

def irep0018Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(10,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0018Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0018Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0018Node0Reductions irep0018Node0Children

theorem irep0018_cached_checked :
    irep0018Node0.check (cachedIntegerProblem irep0018State) (integerInitialRows irep0018State) = true := by
  decide +kernel

theorem irep0018_checked :
    irep0018Node0.check (integerProblem irep0018State) (integerInitialRows irep0018State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0018_cached_checked

theorem irep0018_solved : Solved irep0018State :=
  solved_of_integer_certificate irep0018State irep0018Node0 irep0018_checked

theorem irep0018_representative : Solved (stateEquiv (representativeCode 18)) := by
  have he : stateEquiv (representativeCode 18) = irep0018State := by decide +kernel
  rw [he]
  exact irep0018_solved

def irep0019State : DirectionTriple := ![none,some (directionEquiv 0),some (directionEquiv 18)]

def irep0019Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0019Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0019Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0019Node0Reductions irep0019Node0Children

theorem irep0019_cached_checked :
    irep0019Node0.check (cachedIntegerProblem irep0019State) (integerInitialRows irep0019State) = true := by
  decide +kernel

theorem irep0019_checked :
    irep0019Node0.check (integerProblem irep0019State) (integerInitialRows irep0019State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0019_cached_checked

theorem irep0019_solved : Solved irep0019State :=
  solved_of_integer_certificate irep0019State irep0019Node0 irep0019_checked

theorem irep0019_representative : Solved (stateEquiv (representativeCode 19)) := by
  have he : stateEquiv (representativeCode 19) = irep0019State := by decide +kernel
  rw [he]
  exact irep0019_solved

def irep0020State : DirectionTriple := ![none,some (directionEquiv 1),none]

def irep0020Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0020Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0020Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0020Node0Reductions irep0020Node0Children

theorem irep0020_cached_checked :
    irep0020Node0.check (cachedIntegerProblem irep0020State) (integerInitialRows irep0020State) = true := by
  decide +kernel

theorem irep0020_checked :
    irep0020Node0.check (integerProblem irep0020State) (integerInitialRows irep0020State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0020_cached_checked

theorem irep0020_solved : Solved irep0020State :=
  solved_of_integer_certificate irep0020State irep0020Node0 irep0020_checked

theorem irep0020_representative : Solved (stateEquiv (representativeCode 20)) := by
  have he : stateEquiv (representativeCode 20) = irep0020State := by decide +kernel
  rw [he]
  exact irep0020_solved

def irep0021State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 0)]

def irep0021Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0021Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0021Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0021Node0Reductions irep0021Node0Children

theorem irep0021_cached_checked :
    irep0021Node0.check (cachedIntegerProblem irep0021State) (integerInitialRows irep0021State) = true := by
  decide +kernel

theorem irep0021_checked :
    irep0021Node0.check (integerProblem irep0021State) (integerInitialRows irep0021State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0021_cached_checked

theorem irep0021_solved : Solved irep0021State :=
  solved_of_integer_certificate irep0021State irep0021Node0 irep0021_checked

theorem irep0021_representative : Solved (stateEquiv (representativeCode 21)) := by
  have he : stateEquiv (representativeCode 21) = irep0021State := by decide +kernel
  rw [he]
  exact irep0021_solved

def irep0022State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 1)]

def irep0022Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(11,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(11,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0022Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0022Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0022Node0Reductions irep0022Node0Children

theorem irep0022_cached_checked :
    irep0022Node0.check (cachedIntegerProblem irep0022State) (integerInitialRows irep0022State) = true := by
  decide +kernel

theorem irep0022_checked :
    irep0022Node0.check (integerProblem irep0022State) (integerInitialRows irep0022State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0022_cached_checked

theorem irep0022_solved : Solved irep0022State :=
  solved_of_integer_certificate irep0022State irep0022Node0 irep0022_checked

theorem irep0022_representative : Solved (stateEquiv (representativeCode 22)) := by
  have he : stateEquiv (representativeCode 22) = irep0022State := by decide +kernel
  rw [he]
  exact irep0022_solved

def irep0023State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 2)]

def irep0023Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0023Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0023Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0023Node0Reductions irep0023Node0Children

theorem irep0023_cached_checked :
    irep0023Node0.check (cachedIntegerProblem irep0023State) (integerInitialRows irep0023State) = true := by
  decide +kernel

theorem irep0023_checked :
    irep0023Node0.check (integerProblem irep0023State) (integerInitialRows irep0023State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0023_cached_checked

theorem irep0023_solved : Solved irep0023State :=
  solved_of_integer_certificate irep0023State irep0023Node0 irep0023_checked

theorem irep0023_representative : Solved (stateEquiv (representativeCode 23)) := by
  have he : stateEquiv (representativeCode 23) = irep0023State := by decide +kernel
  rw [he]
  exact irep0023_solved

def irep0024State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 4)]

def irep0024Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0024Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0024Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0024Node0Reductions irep0024Node0Children

theorem irep0024_cached_checked :
    irep0024Node0.check (cachedIntegerProblem irep0024State) (integerInitialRows irep0024State) = true := by
  decide +kernel

theorem irep0024_checked :
    irep0024Node0.check (integerProblem irep0024State) (integerInitialRows irep0024State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0024_cached_checked

theorem irep0024_solved : Solved irep0024State :=
  solved_of_integer_certificate irep0024State irep0024Node0 irep0024_checked

theorem irep0024_representative : Solved (stateEquiv (representativeCode 24)) := by
  have he : stateEquiv (representativeCode 24) = irep0024State := by decide +kernel
  rw [he]
  exact irep0024_solved

def irep0025State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 5)]

def irep0025Node1Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 4, weights := [(1,(⟨(2),(0)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 1, weights := [(2,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0025Node1Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0025Node1 : Certificate 4 64 60 48 960 :=
  .split 6 irep0025Node1Reductions irep0025Node1Children

def irep0025Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0],![0,0,1,(⟨(0),(1)⟩ : GZ)]], witnesses := fun i => ([{ denominator := 1, weights := [(1,1)] },{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0025Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![irep0025Node1,
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0025Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0025Node0Reductions irep0025Node0Children

theorem irep0025_cached_checked :
    irep0025Node0.check (cachedIntegerProblem irep0025State) (integerInitialRows irep0025State) = true := by
  decide +kernel

theorem irep0025_checked :
    irep0025Node0.check (integerProblem irep0025State) (integerInitialRows irep0025State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0025_cached_checked

theorem irep0025_solved : Solved irep0025State :=
  solved_of_integer_certificate irep0025State irep0025Node0 irep0025_checked

theorem irep0025_representative : Solved (stateEquiv (representativeCode 25)) := by
  have he : stateEquiv (representativeCode 25) = irep0025State := by decide +kernel
  rw [he]
  exact irep0025_solved

def irep0026State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 6)]

def irep0026Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0026Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0026Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0026Node0Reductions irep0026Node0Children

theorem irep0026_cached_checked :
    irep0026Node0.check (cachedIntegerProblem irep0026State) (integerInitialRows irep0026State) = true := by
  decide +kernel

theorem irep0026_checked :
    irep0026Node0.check (integerProblem irep0026State) (integerInitialRows irep0026State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0026_cached_checked

theorem irep0026_solved : Solved irep0026State :=
  solved_of_integer_certificate irep0026State irep0026Node0 irep0026_checked

theorem irep0026_representative : Solved (stateEquiv (representativeCode 26)) := by
  have he : stateEquiv (representativeCode 26) = irep0026State := by decide +kernel
  rw [he]
  exact irep0026_solved

def irep0027State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 8)]

def irep0027Node3Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0027Node3Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0027Node3 : Certificate 4 64 60 48 960 :=
  .split 5 irep0027Node3Reductions irep0027Node3Children

def irep0027Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 4, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,(⟨(2),(0)⟩ : GZ)],![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] },{ denominator := 1, weights := [(1,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0027Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    irep0027Node3,
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] }]

def irep0027Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0027Node0Reductions irep0027Node0Children

theorem irep0027_cached_checked :
    irep0027Node0.check (cachedIntegerProblem irep0027State) (integerInitialRows irep0027State) = true := by
  decide +kernel

theorem irep0027_checked :
    irep0027Node0.check (integerProblem irep0027State) (integerInitialRows irep0027State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0027_cached_checked

theorem irep0027_solved : Solved irep0027State :=
  solved_of_integer_certificate irep0027State irep0027Node0 irep0027_checked

theorem irep0027_representative : Solved (stateEquiv (representativeCode 27)) := by
  have he : stateEquiv (representativeCode 27) = irep0027State := by decide +kernel
  rw [he]
  exact irep0027_solved

def irep0028State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 9)]

def irep0028Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0028Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0028Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0028Node0Reductions irep0028Node0Children

theorem irep0028_cached_checked :
    irep0028Node0.check (cachedIntegerProblem irep0028State) (integerInitialRows irep0028State) = true := by
  decide +kernel

theorem irep0028_checked :
    irep0028Node0.check (integerProblem irep0028State) (integerInitialRows irep0028State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0028_cached_checked

theorem irep0028_solved : Solved irep0028State :=
  solved_of_integer_certificate irep0028State irep0028Node0 irep0028_checked

theorem irep0028_representative : Solved (stateEquiv (representativeCode 28)) := by
  have he : stateEquiv (representativeCode 28) = irep0028State := by decide +kernel
  rw [he]
  exact irep0028_solved

def irep0029State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 10)]

def irep0029Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(16,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(3)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0029Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0029Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0029Node0Reductions irep0029Node0Children

theorem irep0029_cached_checked :
    irep0029Node0.check (cachedIntegerProblem irep0029State) (integerInitialRows irep0029State) = true := by
  decide +kernel

theorem irep0029_checked :
    irep0029Node0.check (integerProblem irep0029State) (integerInitialRows irep0029State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0029_cached_checked

theorem irep0029_solved : Solved irep0029State :=
  solved_of_integer_certificate irep0029State irep0029Node0 irep0029_checked

theorem irep0029_representative : Solved (stateEquiv (representativeCode 29)) := by
  have he : stateEquiv (representativeCode 29) = irep0029State := by decide +kernel
  rw [he]
  exact irep0029_solved

def irep0030State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 16)]

def irep0030Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0030Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0030Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0030Node0Reductions irep0030Node0Children

theorem irep0030_cached_checked :
    irep0030Node0.check (cachedIntegerProblem irep0030State) (integerInitialRows irep0030State) = true := by
  decide +kernel

theorem irep0030_checked :
    irep0030Node0.check (integerProblem irep0030State) (integerInitialRows irep0030State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0030_cached_checked

theorem irep0030_solved : Solved irep0030State :=
  solved_of_integer_certificate irep0030State irep0030Node0 irep0030_checked

theorem irep0030_representative : Solved (stateEquiv (representativeCode 30)) := by
  have he : stateEquiv (representativeCode 30) = irep0030State := by decide +kernel
  rw [he]
  exact irep0030_solved

def irep0031State : DirectionTriple := ![none,some (directionEquiv 1),some (directionEquiv 17)]

def irep0031Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0031Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def irep0031Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0031Node0Reductions irep0031Node0Children

theorem irep0031_cached_checked :
    irep0031Node0.check (cachedIntegerProblem irep0031State) (integerInitialRows irep0031State) = true := by
  decide +kernel

theorem irep0031_checked :
    irep0031Node0.check (integerProblem irep0031State) (integerInitialRows irep0031State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0031_cached_checked

theorem irep0031_solved : Solved irep0031State :=
  solved_of_integer_certificate irep0031State irep0031Node0 irep0031_checked

theorem irep0031_representative : Solved (stateEquiv (representativeCode 31)) := by
  have he : stateEquiv (representativeCode 31) = irep0031State := by decide +kernel
  rw [he]
  exact irep0031_solved

theorem representativeBatch001 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (Fin.ofNat 4045 (16*1+i.val)))) := by
  fin_cases i
  · exact irep0016_representative
  · exact irep0017_representative
  · exact irep0018_representative
  · exact irep0019_representative
  · exact irep0020_representative
  · exact irep0021_representative
  · exact irep0022_representative
  · exact irep0023_representative
  · exact irep0024_representative
  · exact irep0025_representative
  · exact irep0026_representative
  · exact irep0027_representative
  · exact irep0028_representative
  · exact irep0029_representative
  · exact irep0030_representative
  · exact irep0031_representative

end
end Holant.Pauli.ExoticKlein.SixPort
