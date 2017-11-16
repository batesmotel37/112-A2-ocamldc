(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)
open Printf

module Bigint = struct

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list
    let  radix    = 10
    let  radixlen =  1

    let car       = List.hd
    let cdr       = List.tl
    let map       = List.map
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, [])

    let charlist_of_string str = 
        let last = strlen str - 1
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)

    let string_of_bigint (Bigint (sign, value)) = match value with
        | []       -> "0"
        | car::cdr ->
                      let rec string_of_bigint' value' charcount' = 
                                                       match value' with
                          | []       -> []
                          | car::cdr -> 
                            if charcount' = 68
                            then (string_of_int car) :: "\\" :: "\n"
                                 :: (string_of_bigint' cdr 0)
                            else (string_of_int car) :: 
                                (string_of_bigint' cdr (charcount' + 1))
                      in strcat "" ((if sign = Pos then "" else "-") ::
                                  (string_of_bigint' (reverse value) 0))

    (*taken from trimzeros.ml provided by Prof. Mackey*)
    let trimzeros list =
        let rec trimzeros' list' = match list' with
            | []       -> []
            | [0]      -> []
            | car::cdr ->
                 let cdr' = trimzeros' cdr
                 in  match car, cdr' with
                     | 0, [] -> []
                     | car, cdr' -> car::cdr'
        in trimzeros' list

    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)

    let rec sub' list1 list2 carry = match (list1, list2,carry) with
        | list1, [], 0                  -> list1
        | [], list2, 0                  -> list2
        | list1, [], carry              -> sub' list1 [carry] 0
        | [], list2, carry              -> sub' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
          let diff = car1 - carry - car2
          in
          if diff >= 0 (*car1 - carry >= car2*) 
          then let result = diff :: sub' cdr1 cdr2 0
               in trimzeros result
          else let result = 10 + diff :: sub' cdr1 cdr2 1
               in trimzeros result

    let rec cmp' list1 list2 returnBit = match (list1,list2) with
        | [],[]                  -> returnBit
        | list1,[]               -> 1
        | [],list2               -> -1
        | car1::cdr1, car2::cdr2 -> 
          if car1 > car2 then cmp' cdr1 cdr2 1
          else if car1 = car2 then cmp' cdr1 cdr2 returnBit
          else cmp' cdr1 cdr2 (-1)

    let cmp list1 list2 =
        cmp' list1 list2 0

    let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg1 = neg2
        then Bigint (neg1, add' value1 value2 0)
        else if cmp value1 value2 >= 0 
        then Bigint (neg1, sub' value1 value2 0)
        else Bigint (neg2, sub' value2 value1 0)

    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg2 = Pos
        then add (Bigint (neg1, value1)) (Bigint (Neg, value2))
        else add (Bigint (neg1, value1)) (Bigint (Pos, value2))

    (* mul', mul, div, rem, divrem and divrem' adapted from 
      muldivrem-trace.ml provided by Prof. Mackey *)

    let rec mul' (multiplier, powerof2, multiplicand') =
        if cmp powerof2 multiplier > 0
        then multiplier, []
        else let remainder, product = 
                 mul' (multiplier, add' powerof2 powerof2 0, 
                                   add' multiplicand' multiplicand' 0)
             in if cmp remainder powerof2 < 0
                then remainder, product
                else sub' remainder powerof2 0, 
                     add' product multiplicand' 0

    let mul (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let _,product = mul' (value1, [1], value2)
        in if neg1 = neg2
        then (Bigint (Pos, product))
        else (Bigint (Neg, product))

    let rec divrem' (dividend, powerof2, divisor') =
        if cmp divisor' dividend > 0
        then [], dividend
        else let quotient, remainder =
                 divrem' (dividend, add' powerof2 powerof2 0, 
                                    add' divisor' divisor' 0)
             in if cmp remainder divisor' < 0
                then quotient, remainder
                else add' quotient powerof2 0, sub' remainder divisor' 0

    let divrem list1 list2' = divrem' (list1, [1], list2')

    let div (Bigint (neg1, value1)) (Bigint (neg2, value2)) = 
        let quotient, _ = divrem value1 value2
        in if neg1 = neg2
        then (Bigint (Pos, quotient))
        else (Bigint (Neg, quotient))

    let rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let _, remainder = divrem value1 value2
        in (Bigint (neg1, remainder))

    (*pow' and pow adapted from Prof. Mackey's mathfns-trace.ml*)

    let rec pow' (list1, list2, result) = match list2 with
        | []    -> result
        | list2 -> let _, mod2 = divrem' (list2, [1], [2]) in
                if mod2 = []
                then let div2, _ = divrem' (list2, [1], [2])
                     in let _, square = mul' (list1, [1], list1) in
                         pow' (square, div2, result)
                else let _, product = mul' (list1, [1], result) in
                         pow' (list1, sub' list2 [1] 0, product)

    let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg2 = Neg
        then if value1 = [1]
             then if neg1 = Pos
                  then (Bigint (Pos, [1]))
                  else (*zero if neg1 = Neg
                       then*) (Bigint (Neg, [1]))
             else zero
        else 
             let _,even = divrem' (value2, [1], [2])
             in if neg1 = Neg && even = [1]
                then (Bigint (Neg, pow' (value1, value2, [1])))
                else (Bigint (Pos, pow' (value1, value2, [1])))

end
