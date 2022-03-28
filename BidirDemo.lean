def hello := "world"

def Name := Nat

instance : BEq Name where
  beq := Nat.beq


inductive SType
  | tbool
  | tfun : SType -> SType -> SType
  deriving Repr

def SType.beq : SType -> SType -> Bool
  | tbool, tbool => true
  | tfun τ1 τ2, tfun σ1 σ2 => (beq τ1 σ1) && (beq τ1 σ2)
  | _, _ => false

instance : BEq SType where
  beq := SType.beq

inductive STerm
  | var : Name -> STerm
  | app : STerm -> STerm -> STerm
  | abs : Name -> STerm -> STerm
  | strue
  | sfalse
  | ite : STerm -> STerm -> STerm -> STerm
  | ann : STerm -> SType -> STerm
  deriving Repr

def Ctx := List (Name × SType)

mutual
  open STerm
  open SType

  partial def check (Γ : Ctx) (t : STerm) (τ : SType) : Bool :=
    match t with
    | abs n t1 =>
        match τ with
        | tfun τ1 τ2 => check (List.cons ⟨n, τ1⟩ Γ) t1 τ2
        | _ => false
    | STerm.ite t1 t2 t3 =>
        (check Γ t1 tbool) && (check Γ t2 τ) && (check Γ t3 τ)
    | _ => match synth Γ t with
           | some τ1 => τ == τ1
           | none    => false

  partial def synth (Γ : Ctx) (t : STerm) : Option SType :=
    match t with
    | var n => Γ.lookup n
    | app t1 t2 =>
        match synth Γ t1 with
        | some (tfun τ1 τ2) => if check Γ t2 τ1 then some τ2 else none
        | _ => none
    | strue | sfalse => some tbool
    | ann t1 τ => if check Γ t1 τ then some τ else none
    | _ => none
end

namespace examples

open STerm
open SType

instance : OfNat Name n where
  ofNat := n

-- λ f . λ g . λ b . g (f b) : (Bool → Bool) → (Bool → Bool) → Bool → Bool
def f : Name := 1
def g : Name := 2
def b : Name := 3
def body :=
  abs f (
    abs g (
      abs b (
        app (var g) (app (var f) (var b))
      )
    )
  )
def btob := tfun tbool tbool
def τ := tfun btob (tfun btob (tfun tbool tbool))
def ex1 := ann body τ

#eval synth [] ex1

end examples
