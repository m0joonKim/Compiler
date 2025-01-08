module P6

/// From list 'l', find the element that appears most frequently in the list,
/// and return how many times it appears. If the input list is empty, return 0.


let rec maxHelper (acc: int) (m1: Map<'a,int>) (l1: List<'a>) : int=
  match l1 with
  | [] -> acc
  | head :: tail -> 
    let now = Map.find head m1
    if now > acc then maxHelper now m1 tail else maxHelper acc m1 tail
    
let rec LtoM (l: List<'a>) : Map<'a,int> = 
  match l with
  | [] -> Map.empty;
  | head :: tail -> 
    let m1 : Map<'a,int> = LtoM tail
    if Map.containsKey head m1 then Map.add head (Map.find head m1 + 1) m1 else Map.add head 1 m1
let rec countMostFrequent (l: List<'a>) : int =
  let m1 : Map<'a,int> = LtoM l
  maxHelper 0 m1 l
