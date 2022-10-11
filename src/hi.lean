import data.bitvec.basic

-- shl
-- lshr -> ushr
-- ashr -> sshr
-- and
-- not
-- xor
-- add
-- sub
-- ult
-- slt
-- ugt
-- sgt


section REWRITES1
variable n : nat
variable X : bitvec n
variable Y: bitvec n
theorem shl_shl(C1 C2: nat): (X.shl C1).shl C2 = X.shl (C1 + C2) := by sorry
theorem ushr_ushr(C1 C2: nat): (X.ushr C1).ushr C2 = X.ushr (C1 + C2) := by sorry
theorem shl_ushr(C: nat): ∃ C', -- TODO: find correct expression for C'.
    (X.shl C).ushr C = X.and C' := by sorry
theorem ushr_ushl(C: nat): ∃ C', -- TODO: find correct expression for C'.
    (X.ushr C).shl C = X.and C' := by sorry
theorem ushr_shl_as_and (C: nat): ∃ C', (X.ushr C).shl C = X.and C' := by sorry

/-
  TODO: I am unsure what the C3 is supposed to be.
    ushr (shl X, C1), C2 =  and (shl X, C1 - C2), C3
    shl (ushr X, C1), C2 = and (ushr X, C1 - C2), C3
-/
end REWRITES1

section REWRITES2
/-
All the patterns are equal to `x & ShiftShAmt`,
- 1 `(x & ((1 << MaskShAmt) - 1)) << ShiftShAmt`.
- 2 `(x & (~(-1 << MaskShAmt))) << ShiftShAmt`.
- 3 `(x & (-1 l>> MaskShAmt)) << ShiftShAmt`.
- 4 `(x & ((-1 << MaskShAmt) l>> MaskShAmt)) << ShiftShAmt`.
- 5 `((x << MaskShAmt) l>> MaskShAmt) << ShiftShAmt`.
- 6 `((x << MaskShAmt) a>> MaskShAmt) << ShiftShAmt`.
- 7 `C << (X - AddC) = (C >> AddC) << X`.
- 8 `C >> (X - AddC) = (C << AddC) >> X`.
-/

variable n: nat
variable X: bitvec n
variable MaskShAmt: nat
variable ShiftShAmt: nat

def bitvec.minusone (n : ℕ) : bitvec n := vector.repeat tt n


-- `(x & ((1 << MaskShAmt) - 1)) << ShiftShAmt = x & ShiftShAmt`.
def thm1 : (X.and (((bitvec.one n).shl MaskShAmt).sub (bitvec.one n))).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry

-- `(x & (~(-1 << MaskShAmt))) << ShiftShAmt = x & ShiftShAmt`.
def thm2 : (X.and ((bitvec.minusone n).shl MaskShAmt).not).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry

-- 3 `(x & (-1 l>> MaskShAmt)) << ShiftShAmt = x & ShiftShAmt`.
def thm3 : (X.and ((bitvec.minusone n).ushr MaskShAmt)).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry
-- 4 `(x & ((-1 << MaskShAmt) l>> MaskShAmt)) << ShiftShAmt = x & ShiftShAmt`.
def thm4 : (X.and (((bitvec.minusone n).shl MaskShAmt).ushr MaskShAmt)).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry
-- 5 `((x << MaskShAmt) l>> MaskShAmt) << ShiftShAmt = x & ShiftShAmt`.
def thm5 : ((X.shl MaskShAmt).ushr MaskShAmt).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry
-- 6 `((x << MaskShAmt) a>> MaskShAmt) << ShiftShAmt = x & ShiftShAmt`.
def thm6 : ((X.shl MaskShAmt).sshr MaskShAmt).shl ShiftShAmt =
   X.and ((bitvec.one n).shl ShiftShAmt) := by sorry

/-
-- These need X to be treated as a number, and C as a bitvector. Leave for later.
-- 7 `C << (X - AddC) = (C >> AddC) << X = x & ShiftShAmt`.
-- 8 `C >> (X - AddC) = (C << AddC) >> X = x & ShiftShAmt`.
-/
end REWRITES2



def hellom : string := "hello"

#eval hellom