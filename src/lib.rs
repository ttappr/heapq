//! ## Heap queue algorithm (a.k.a. priority queue).
//!
//! Heaps are arrays for which `a[k] <= a[2*k+1]` and `a[k] <= a[2*k+2]` for
//! all `k`, counting elements from `0`.  For the sake of comparison,
//! non-existing elements are considered to be infinite.  The interesting
//! property of a heap is that `a[0]` is always its smallest element.
//!
//! Usage:
//! 
//! ```rust,ignore
//! // create an empty heap
//! let mut heap = vec![];
//!
//! // push a new item on the heap
//! heap_push(&mut heap, item);
//!
//! // pop the smallest item from the heap
//! let item = heap_pop(&mut heap);
//!
//! // get the smallest item on the heap without popping it
//! let item = &heap[0];
//!
//! // transform slice into a heap, in-place, in linear time
//! heapify(&mut x);
//!
//! // push a new item and then returns the smallest item; the heap size is
//! // unchanged
//! item = heap_pushpop(&mut heap, item);
//!
//! // pop and returns smallest item, and adds new item; the heap size is
//! // unchanged
//! item = heap_replace(&mut heap, item);
//! ```
//! 
//! Our API differs from textbook heap algorithms as follows:
//!
//! - We use 0-based indexing.  This makes the relationship between the
//!   index for a node and the indexes for its children slightly less
//!   obvious, but is more suitable since Rust uses 0-based indexing.
//! - Our `heap_pop()` method returns the smallest item, not the largest.
//!
//! These two make it possible to view the heap as a regular Rust slice
//! without surprises: `heap[0]` is the smallest item, and `heap.sort()`
//! maintains the heap invariant!
//!
//! ## Heap queues
//!
//! *explanation by François Pinard*
//!
//! Heaps are arrays for which `a[k] <= a[2*k+1]` and `a[k] <= a[2*k+2]` for
//! all `k`, counting elements from `0`.  For the sake of comparison,
//! non-existing elements are considered to be infinite.  The interesting
//! property of a heap is that `a[0]` is always its smallest element.
//!
//! The strange invariant above is meant to be an efficient memory
//! representation for a tournament.  The numbers below are `k`, not `a[k]`:
//! ```ignore
//!                                    0
//!
//!                   1                                 2
//!
//!           3               4                5               6
//!
//!       7       8       9       10      11      12      13      14
//!
//!     15 16   17 18   19 20   21 22   23 24   25 26   27 28   29 30
//! ```
//!
//! In the tree above, each cell `k` is topping `2*k+1` and `2*k+2`.  In
//! a usual binary tournament we see in sports, each cell is the winner
//! over the two cells it tops, and we can trace the winner down the tree
//! to see all opponents s/he had.  However, in many computer applications
//! of such tournaments, we do not need to trace the history of a winner.
//! To be more memory efficient, when a winner is promoted, we try to
//! replace it by something else at a lower level, and the rule becomes
//! that a cell and the two cells it tops contain three different items,
//! but the top cell "wins" over the two topped cells.
//!
//! If this heap invariant is protected at all time, index 0 is clearly
//! the overall winner.  The simplest algorithmic way to remove it and
//! find the "next" winner is to move some loser (let's say cell 30 in the
//! diagram above) into the 0 position, and then percolate this new 0 down
//! the tree, exchanging values, until the invariant is re-established.
//! This is clearly logarithmic on the total number of items in the tree.
//! By iterating over all items, you get an `O(n ln n)` sort.
//!
//! A nice feature of this sort is that you can efficiently insert new
//! items while the sort is going on, provided that the inserted items are
//! not "better" than the last 0'th element you extracted.  This is
//! especially useful in simulation contexts, where the tree holds all
//! incoming events, and the "win" condition means the smallest scheduled
//! time.  When an event schedule other events for execution, they are
//! scheduled into the future, so they can easily go into the heap.  So, a
//! heap is a good structure for implementing schedulers (this is what I
//! used for my MIDI sequencer :-).
//!
//! Various structures for implementing schedulers have been extensively
//! studied, and heaps are good for this, as they are reasonably speedy,
//! the speed is almost constant, and the worst case is not much different
//! than the average case.  However, there are other representations which
//! are more efficient overall, yet the worst cases might be terrible.
//!
//! Heaps are also very useful in big disk sorts.  You most probably all
//! know that a big sort implies producing "runs" (which are pre-sorted
//! sequences, which size is usually related to the amount of CPU memory),
//! followed by a merging passes for these runs, which merging is often
//! very cleverly organised[^1].  It is very important that the initial
//! sort produces the longest runs possible.  Tournaments are a good way
//! to that.  If, using all the memory available to hold a tournament, you
//! replace and percolate items that happen to fit the current run, you'll
//! produce runs which are twice the size of the memory for random input,
//! and much better for input fuzzily ordered.
//!
//! Moreover, if you output the 0'th item on disk and get an input which
//! may not fit in the current tournament (because the value "wins" over
//! the last output value), it cannot fit in the heap, so the size of the
//! heap decreases.  The freed memory could be cleverly reused immediately
//! for progressively building a second heap, which grows at exactly the
//! same rate the first heap is melting.  When the first heap completely
//! vanishes, you switch heaps and start a new run.  Clever and quite
//! effective!
//!
//! In a word, heaps are useful memory structures to know.  I use them in
//! a few applications, and I think it is good to keep a `heap` module
//! around. :-)
//!
//! [^1]: The disk balancing algorithms which are current, nowadays, are
//! more annoying than clever, and this is a consequence of the seeking
//! capabilities of the disks.  On devices which cannot seek, like big
//! tape drives, the story was quite different, and one had to be very
//! clever to ensure (far in advance) that each tape movement will be the
//! most effective possible (that is, will best participate at
//! "progressing" the merge).  Some tapes were even able to read
//! backwards, and this was also used to avoid the rewinding time.
//! Believe me, real good tape sorts were quite spectacular to watch!
//! From all times, sorting has always been a Great Art! :-)

use std::cmp::Ordering::{self, Less};


/// Transform slice into a heap, in-place, in O(n) time.
/// # Examples
/// ```rust
/// use heapq::*;
/// 
/// let mut heap = vec![3, 8, 0, 7, 6, 5, 2, 1, 4, 9];
/// let sorted = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
///
/// heapify(&mut heap);
///
/// let mut result = Vec::with_capacity(heap.len());
///
/// while let Some(v) = heap_pop(&mut heap) {
///    result.push(v);
/// }
/// assert_eq!(result, sorted);
/// ```
#[inline]
pub fn heapify<T>(heap: &mut [T])
where
    T: Ord
{
    heapify_with(heap, T::cmp);
}

/// Transform slice into a heap in place using `cmp` for comparisons.
///
#[inline]
pub fn heapify_with<T, C>(heap: &mut [T], cmp: C)
where
    C: Fn(&T, &T) -> Ordering
{
    heapify_with_aux(heap, |a, b, _| cmp(a, b), ());
}

/// Transform slice into a heap in place using `cmp` for comparisons. The `aux`
/// parameter allows passing aribitrary data to `cmp`. This could be a
/// reference to another related structure needed for comparisons.
///
/// # Examples
/// ```rust
/// use heapq::*;
/// 
/// let values = [17, 42, 1, 8, 71, 241, 122];
/// 
/// let mut index_heap = (0..values.len()).collect::<Vec<_>>();
/// 
/// let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);
/// 
/// heapify_with_aux(&mut index_heap, cmp, &values);
/// 
/// let item_idx = heap_pop_with_aux(&mut index_heap, cmp, &values).unwrap();
/// let item = values[item_idx];
/// 
/// assert_eq!(item, 1);
/// 
/// let item_idx = heap_pop_with_aux(&mut index_heap, cmp, &values).unwrap();
/// let item = values[item_idx];
/// 
/// assert_eq!(item, 8);
/// ```
/// 
pub fn heapify_with_aux<T, C, A>(heap: &mut [T], cmp: C, aux: A)
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    for i in (0..heap.len() / 2).rev() {
        sift_up(heap, i, &cmp, aux);
    }
}

/// Push item onto heap, maintaining the heap invariant.
/// # Examples
/// ```rust
/// use heapq::*;
/// 
/// let vals   = vec![3, 8, 0, 7, 6, 5, 2, 1, 4, 9];
/// let sorted = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
/// 
/// let mut heap = Vec::with_capacity(vals.len());
/// let mut result = Vec::with_capacity(vals.len());
///
/// for val in vals {
///    heap_push(&mut heap, val);
/// }
/// while let Some(v) = heap_pop(&mut heap) {
///    result.push(v);
/// }
/// assert_eq!(result, sorted);
/// ```
#[inline]
pub fn heap_push<T>(heap: &mut Vec<T>, item: T)
where
    T: Ord
{
    heap_push_with(heap, item, T::cmp);
}

/// Push item onto the heap using the comparison function `cmp`.
///
#[inline]
pub fn heap_push_with<T, C>(heap: &mut Vec<T>, item: T, cmp: C)
where
    C: Fn(&T, &T) -> Ordering
{
    heap_push_with_aux(heap, item, |a, b, _| cmp(a, b), ());
}

/// Push the item onto the heap using the comparison function `cmp` with
/// auxiliary data `aux` to be passed to `cmp`.
///
pub fn heap_push_with_aux<T, C, A>(heap: &mut Vec<T>, item: T, cmp: C, aux: A)
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    let len = heap.len();
    heap.push(item);
    sift_down(heap, 0, len, cmp, aux);
}

/// Pop the smallest item off the heap, maintaining the heap invariant.
/// # Examples
/// ```rust
/// use heapq::*;
/// 
/// let mut heap = vec![5, 8, 1, 4, 2];
///
/// heapify(&mut heap);
///
/// assert_eq!(heap_pop(&mut heap), Some(1));
/// assert_eq!(heap_pop(&mut heap), Some(2));
/// ```
#[inline]
pub fn heap_pop<T>(heap: &mut Vec<T>) -> Option<T>
where
    T: Ord
{
    heap_pop_with(heap, T::cmp)
}

/// Pop the smallest item off the heap and maintain the invariant using the
/// comparison function `cmp`.
///
#[inline]
pub fn heap_pop_with<T, C>(heap: &mut Vec<T>, cmp: C) -> Option<T>
where
    C: Fn(&T, &T) -> Ordering
{
    heap_pop_with_aux(heap, |a, b, _| cmp(a, b), ())
}

/// Pop the smallest item off the heap, maintaining the invariant using `cmd`
/// which accepts auxiliary data `aux` on each call.
///
pub fn heap_pop_with_aux<T, C, A>(heap: &mut Vec<T>, cmp: C, aux: A)

    -> Option<T>
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    if !heap.is_empty() {
        let returnitem = heap.swap_remove(0);
        sift_up(heap, 0, cmp, aux);
        Some(returnitem)
    } else {
        None
    }
}

/// Fast version of a heap_push followed by a heap_pop.
/// ```rust
/// use heapq::*;
/// 
/// let mut heap = vec![5, 8, 1, 4, 2];
///
/// heapify(&mut heap);
///
/// assert_eq!(heap_pushpop(&mut heap, 0), 0);
/// assert_eq!(heap_pushpop(&mut heap, 7), 1);
/// ```
#[inline]
pub fn heap_pushpop<T>(heap: &mut [T], item: T) -> T 
where
    T: Ord
{
    heap_pushpop_with(heap, item, T::cmp)
}

/// Fast version of a heap_push followed by a heap_pop that takes a comparator
/// for instances of `T`.
/// 
#[inline]
pub fn heap_pushpop_with<T, C>(heap: &mut [T], item: T, cmp: C) -> T
where 
    C: Fn(&T, &T) -> Ordering
{
    heap_pushpop_with_aux(heap, item, |a, b, _| cmp(a, b), ())
}

/// Fast version of a heap_push followed by a heap_pop that takes a comparison
/// function and auxiliary data that gets passed to `cmp` on each call.
/// 
pub fn heap_pushpop_with_aux<T, C, A>(heap : &mut [T], 
                                      item : T, 
                                      cmp  : C, 
                                      aux  : A) 
    -> T
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    if !heap.is_empty() && cmp(&heap[0], &item, aux) == Less {
        let item = std::mem::replace(&mut heap[0], item);
        sift_up(heap, 0, cmp, aux);
        item
    } else {
        item
    }
}

/// Pops an item from the heap and pushes the new item onto it. The popped item
/// is returned.
/// # Examples
/// ```rust
/// use heapq::*;
/// let mut heap = [5, 8, 1, 4, 2];
///
/// heapify(&mut heap);
///
/// assert_eq!(heap_replace(&mut heap, 0), 1);
/// assert_eq!(heap_replace(&mut heap, 7), 0);
/// assert_eq!(heap_replace(&mut heap, 7), 2);
///
/// heap.sort();
/// assert_eq!(heap, [4, 5, 7, 7, 8]);
/// ```
#[inline]
pub fn heap_replace<T>(heap: &mut [T], item: T) -> T 
where
    T: Ord
{
    heap_replace_with(heap, item, T::cmp)
}

/// Pops an item from the heap, pushes the new item, then returns item. `cmp` is  
/// the comparison function used to maintain the heap.
/// 
#[inline]
pub fn heap_replace_with<T, C>(heap: &mut [T], item: T, cmp: C) -> T 
where
    C: Fn(&T, &T) -> Ordering
{
    heap_replace_with_aux(heap, item, |a, b, _| cmp(a, b), ())
}

/// Pop and return the current smallest value, and add the new item. `cmp` is
/// the heap's comparison function for instances of `T` and `aux` and is 
/// auxiliary data passed to `cmp` when infoked. `aux` can be a reference to
/// another structure needed for the comparisons.
///
/// This is more efficient than heappop() followed by heappush(), and can be
/// more appropriate when using a fixed-size heap.  Note that the value
/// returned may be larger than item!  That constrains reasonable uses of
/// this routine unless written as part of a conditional replacement:
/// ```rust,ignore
///     if item > heap[0] {
///         item = heap_replace(heap, item);
///     }
/// ```
///
pub fn heap_replace_with_aux<T, C, A>(heap : &mut [T], 
                                      item : T, 
                                      cmp  : C, 
                                      aux  : A)
    -> T 
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    if !heap.is_empty() {
        let item = std::mem::replace(&mut heap[0], item);
        sift_up(heap, 0, cmp, aux);
        item
    } else {
        item
    }
}

// The child indices of heap index pos are already heaps, and we want to make
// a heap at index pos too.  We do this by bubbling the smaller child of
// pos up (and so on with that child's children, etc) until hitting a leaf,
// then using _siftdown to move the oddball originally at index pos into place.
//
// We *could* break out of the loop as soon as we find a pos where newitem <=
// both its children, but turns out that's not a good idea, and despite that
// many books write the algorithm that way.  During a heap pop, the last array
// element is sifted in, and that tends to be large, so that comparing it
// against values starting from the root usually doesn't pay (= usually doesn't
// get us out of the loop early).  See Knuth, Volume 3, where this is
// explained and quantified in an exercise.
//
// Cutting the # of comparisons is important, since these routines have no
// way to extract "the priority" from an array element, so that intelligence
// is likely to be hiding in custom comparison methods, or in array elements
// storing (priority, record) tuples.  Comparisons are thus potentially
// expensive.
//
// On random arrays of length 1000, making this change cut the number of
// comparisons made by heapify() a little, and those made by exhaustive
// heappop() a lot, in accord with theory.  Here are typical results from 3
// runs (3 just to demonstrate how small the variance is):
//
// Compares needed by heapify     Compares needed by 1000 heappops
// --------------------------     --------------------------------
// 1837 cut to 1663               14996 cut to 8680
// 1855 cut to 1659               14966 cut to 8678
// 1847 cut to 1660               15024 cut to 8703
//
// Building the heap by using heappush() 1000 times instead required
// 2198, 2148, and 2219 compares:  heapify() is more efficient, when
// you can use it.
//
// The total compares needed by slice.sort() on the same slices were 8627,
// 8627, and 8632 (this should be compared to the sum of heapify() and
// heappop() compares):  slice.sort() is (unsurprisingly!) more efficient
// for sorting.

fn sift_up<T, C, A>(heap: &mut [T], pos: usize, cmp: C, aux: A)
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    let mut pos      = pos;
    let     endpos   = heap.len();
    let     startpos = pos;
    let mut childpos = 2 * pos + 1;

    while childpos < endpos {
        let rightpos = childpos + 1;
        if rightpos < endpos
            && cmp(&heap[childpos], &heap[rightpos], aux) != Less {
            childpos = rightpos;
        }
        heap.swap(pos, childpos);
        pos = childpos;
        childpos = 2 * pos + 1;
    }
    sift_down(heap, startpos, pos, cmp, aux);
}

// 'heap' is a heap at all indices >= startpos, except possibly for pos.  pos
// is the index of a leaf with a possibly out-of-order value.  Restore the
// heap invariant.

fn sift_down<T, C, A>(heap     : &mut [T],
                      startpos : usize,
                      pos      : usize,
                      cmp      : C,
                      aux      : A)
where
    C: Fn(&T, &T, A) -> Ordering,
    A: Copy
{
    let mut pos = pos;

    while pos > startpos {
        let parentpos = (pos - 1) >> 1;

        if cmp(&heap[pos], &heap[parentpos], aux) == Less {
            heap.swap(pos, parentpos);
            pos = parentpos;
        } else {
            break;
        }
    }
}


#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use super::*;

    // The sequence 0 to 99 (inclusive) shuffled.
    const SHUFFLED_INTS: [i32; 100] = [
        23, 22, 55, 87, 59, 27, 90, 14, 82, 21, 44, 75,
        20, 50, 3, 34, 83, 72, 68, 8, 57, 58, 6, 95, 16,
        28, 13, 86, 76, 30, 79, 54, 24, 80, 65, 84, 53,
        78, 67, 56, 18, 93, 61, 42, 10, 77, 40, 2, 71,
        47, 85, 7, 26, 33, 32, 62, 9, 92, 43, 38, 88,
        73, 74, 41, 4, 35, 70, 19, 69, 15, 94, 0, 66,
        39, 31, 63, 89, 5, 25, 99, 91, 51, 98, 97, 1,
        96, 29, 37, 36, 45, 17, 11, 52, 60, 49, 81, 48,
        12, 46, 64
    ];
    const ORDERED_INTS: [i32; 100] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 
        14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 
        36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 
        47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 
        58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 
        69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 
        80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 
        91, 92, 93, 94, 95, 96, 97, 98, 99        
    ];

    fn check_invariant<T>(a: &[T]) -> bool
    where
        T: Ord
    {
        check_invariant_with(a, T::cmp)
    }

    fn check_invariant_with<T, C>(a: &[T], cmp: C) -> bool 
    where
        C: Fn(&T, &T) -> Ordering
    {
        check_invariant_with_aux(a, |a, b, _| cmp(a, b), ())
    }

    fn check_invariant_with_aux<T, C, A>(a: &[T], cmp: C, aux: A) -> bool 
    where
        C: Fn(&T, &T, A) -> Ordering,
        A: Copy
    {
        use Ordering::Greater;

        for k in 0..a.len() / 2 {
            // Heap invariant: a[k] <= a[2*k+1] and a[k] <= a[2*k+2] 
            if !(cmp(&a[k], &a[2 * k + 1], aux) != Greater 
                && cmp(&a[k], &a[2 * k + 2], aux) != Greater) {
                return false;
            }
        }
        true
    }

    #[test]
    fn test_heapify() {
        let mut heap = SHUFFLED_INTS.to_vec();

        heapify(&mut heap);

        let mut result = Vec::with_capacity(heap.len());

        while let Some(v) = heap_pop(&mut heap) {
            result.push(v);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heapify_with() {
        let mut heap = SHUFFLED_INTS.to_vec();
        let cmp = |a: &i32, b: &i32| a.cmp(&b);

        heapify_with(&mut heap, cmp);

        let mut result = Vec::with_capacity(heap.len());

        while let Some(v) = heap_pop_with(&mut heap, cmp) {
            result.push(v);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heapify_with_aux() {
        let mut index_heap = (0..100).collect::<Vec<_>>();
        let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

        heapify_with_aux(&mut index_heap, cmp, &SHUFFLED_INTS);

        let mut result = Vec::with_capacity(index_heap.len());

        while let Some(i) 
            = heap_pop_with_aux(&mut index_heap, cmp, &SHUFFLED_INTS) {
            result.push(SHUFFLED_INTS[i]);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant_with_aux(&index_heap, cmp, &SHUFFLED_INTS));
    }

    #[test]
    fn test_heap_push() {
        let vals = SHUFFLED_INTS.to_vec();

        let mut heap = Vec::with_capacity(vals.len());
        let mut result = Vec::with_capacity(vals.len());

        for val in vals {
            heap_push(&mut heap, val);
        }
        while let Some(v) = heap_pop(&mut heap) {
            result.push(v);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heap_push_with() {
        let vals = SHUFFLED_INTS.to_vec();
        let cmp = |a: &i32, b: &i32| a.cmp(&b);

        let mut heap = Vec::with_capacity(vals.len());
        let mut result = Vec::with_capacity(vals.len());

        for val in vals {
            heap_push_with(&mut heap, val, cmp);
        }
        while let Some(v) = heap_pop_with(&mut heap, cmp) {
            result.push(v);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant_with(&heap, cmp));
    }

    #[test]
    fn test_heap_push_with_aux() {
        let mut index_heap = Vec::with_capacity(100);
        let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

        for i in 0..100 {
            heap_push_with_aux(&mut index_heap, i, cmp, &SHUFFLED_INTS);
        }

        let mut result = Vec::with_capacity(index_heap.len());

        while let Some(i) 
            = heap_pop_with_aux(&mut index_heap, cmp, &SHUFFLED_INTS) {
            result.push(SHUFFLED_INTS[i]);
        }
        assert_eq!(result, ORDERED_INTS);
        assert!(check_invariant_with_aux(&index_heap, cmp, &SHUFFLED_INTS));
    }

    #[test]
    fn test_heap_pushpop() {
        let mut heap = vec![5, 8, 1, 4, 2];

        heapify(&mut heap);

        assert_eq!(heap_pushpop(&mut heap, 0), 0);
        assert_eq!(heap_pushpop(&mut heap, 7), 1);
        assert_eq!(heap_pushpop(&mut heap, 7), 2);
        assert_eq!(heap_pushpop(&mut heap, 7), 4);
        assert_eq!(heap_pushpop(&mut heap, 7), 5);
        assert_eq!(heap_pushpop(&mut heap, 7), 7);
        assert_eq!(heap_pushpop(&mut heap, 7), 7);
        assert_eq!(heap.len(), 5);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heap_pushpop_with() {
        let mut heap = vec![5, 8, 1, 4, 2];
        let cmp = |a: &i32, b: &i32| b.cmp(a); // Make it a max heap.

        heapify_with(&mut heap, cmp);

        assert_eq!(heap_pushpop_with(&mut heap, 0, cmp), 8);
        assert_eq!(heap_pushpop_with(&mut heap, 7, cmp), 7);
        assert_eq!(heap_pushpop_with(&mut heap, 2, cmp), 5);
        assert_eq!(heap_pushpop_with(&mut heap, 2, cmp), 4);
        assert_eq!(heap_pushpop_with(&mut heap, 2, cmp), 2);
        assert_eq!(heap.len(), 5);
        assert!(check_invariant_with(&heap, cmp));
    }

    #[test]
    fn test_heap_pushpop_with_aux() {
        let values = [5, 8, 1, 4, 2];
        let mut index_heap = [1, 4, 3, 0, 2];
        let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

        heapify_with_aux(&mut index_heap, cmp, &values);

        // Note that values on heap are indexes of `values`.
        assert_eq!(heap_pushpop_with_aux(&mut index_heap, 0, cmp, &values), 2);
        assert_eq!(heap_pushpop_with_aux(&mut index_heap, 3, cmp, &values), 4);
        assert!(check_invariant_with_aux(&index_heap, cmp, &values));
    }

    #[test]
    fn test_heap_replace() {
        let mut heap = [5, 8, 1, 4, 2];

        heapify(&mut heap);

        assert_eq!(heap_replace(&mut heap, 0), 1);
        assert_eq!(heap_replace(&mut heap, 7), 0);
        assert_eq!(heap_replace(&mut heap, 7), 2);
        
        heap.sort();
        assert_eq!(heap, [4, 5, 7, 7, 8]);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heap_replace_with() {
        let mut heap = [5, 8, 1, 4, 2];
        let cmp = |a: &i32, b: &i32| a.cmp(b);

        heapify_with(&mut heap, cmp);

        assert_eq!(heap_replace_with(&mut heap, 0, cmp), 1);
        assert_eq!(heap_replace_with(&mut heap, 7, cmp), 0);
        assert_eq!(heap_replace_with(&mut heap, 7, cmp), 2);
        
        heap.sort();
        assert_eq!(heap, [4, 5, 7, 7, 8]);
        assert!(check_invariant(&heap));
    }

    #[test]
    fn test_heap_replace_with_aux() {
        let values = [5, 8, 1, 4, 2];
        let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

        let mut index_heap = [0, 1, 2, 3, 4];

        heapify_with_aux(&mut index_heap, cmp, &values);

        // values[0] == 5. Should get 2 back (values[2] == 1).
        let i = heap_replace_with_aux(&mut index_heap, 0, cmp, &values); 
        assert_eq!(i, 2); 
        assert_eq!(values[i], 1);

        // values[3] == 5. Should get back 4 (values[4] == 2).
        let i = heap_replace_with_aux(&mut index_heap, 3, cmp, &values);
        assert_eq!(i, 4);
        assert_eq!(values[i], 2);
    }

    #[test]
    fn test_time_complexity() {
        // The number of comparisons needed to perform the same operation 100 
        // times on an array of size 100 should be log(n) * 100 if the time 
        // complexity is O(n * log2 n).
        let lim_flat = (100.0_f32.log2().ceil() * 100.0) as i32;

        // The numer of comparisons to perform the same O(log n) operation 100 
        // times on an array that grows from 0 to 100 items or shrinks from 100 
        // to 0 items should have an upper limit of 100 * log2(n).
        let lim_grow = (1..=100).fold(0., |a, n| a + (n as f32).log2().ceil());

        let mut heap = SHUFFLED_INTS.to_vec();

        // Set the comparison counter to 0.
        let count = RefCell::new(0i32);

        let cmp = |a: &i32, b: &i32| { 
            *count.borrow_mut() += 1; // Count the comparison.
            a.cmp(&b) 
        };


        // This should be an O(n) operation applied 100 times.
        heapify_with(&mut heap, cmp);
        
        print!("\n\n");
        println!("The array to be heapified has {} items.", heap.len());
        println!();
        println!("If heapify were O(n * log n), it would take {} \
                  comparisons.", lim_flat);
        println!();
        println!("heapify_with() required {} comparisons.", *count.borrow());

        // Make sure heapify is O(n), or significantly less than O(n * log2 n).
        // The number of comparisons will likely be C * n. Let's use 2 * n 
        // as the upper limit.
        assert!(*count.borrow() <= 200);

        // Reset the comparison counter.
        *count.borrow_mut() = 0;

        // Pop should be an O(log n) operation applied to a shrinking heap.
        while let Some(_) = heap_pop_with(&mut heap, cmp) { }

        print!("\n\n");
        println!("The upper limit for the number of comparisons required to \
                  deplete a heap of 100 items where pop is an O(log n) \
                  operation is {}.", lim_grow);
        println!();
        println!("pop_with() x 100 required {} comparisons.", *count.borrow());
        println!();

        assert!(*count.borrow() <= lim_grow as i32);  
    }

    #[test]
    fn test_readme_code() {
        let heap = &mut Vec::new();
        heap_push(heap, 3);
        heap_push(heap, 1);
        heap_push(heap, 2);
        assert_eq!(heap_pop(heap), Some(1));

        let heap = &mut Vec::new();
        let cmp = |a: &i32, b: &i32| a.cmp(b);

        heap_push_with(heap, 3, cmp);
        heap_push_with(heap, 1, cmp);
        heap_push_with(heap, 2, cmp);
        assert_eq!(heap_pop_with(heap, cmp), Some(1));

        let values = [3, 1, 2];
        let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

        let index_heap = &mut Vec::new();

        // Indexes for items in `values` are pushed onto the heap.
        heap_push_with_aux(index_heap, 0, cmp, &values);
        heap_push_with_aux(index_heap, 1, cmp, &values);
        heap_push_with_aux(index_heap, 2, cmp, &values);

        // Values popped from heap are indexes into `values`.
        assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(1));
        assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(2));
        assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(0));
    }
}