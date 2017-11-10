// Map Tagged Union
var LEAF   = 0,
    TWO    = 1,
    THREE  = 2;

// Tree Context, used when mantain tree
var TWOLEFT     = 0,
    TWORIGHT    = 1,
    THREELEFT   = 2,
    THREEMIDDLE = 3,
    THREERIGHT  = 4;

var NIL  = 0,
    CONS = 1;

var NotFound = 0,
    Found    = 1;

/**
 * 2 tree:
 *        [X]
 *        / \
 *       L   R
 *  3 tree:
 *         [X|Y]
 *        / | \
 *        L M  R
 */
function Map(tag, left, k1, v1, middle, k2, v2, right) {
  if (!(this instanceof Map)) {
    return new Map(tag, left, k1, v1, middle, k2, v2, right);
  }
	this.tag    = tag;
	this.left   = left;
	this.k1     = k1;
	this.v1     = v1;
	this.middle = middle;
	this.k2     = k2;
	this.v2     = v2;
	this.right  = right;
}

// the empty Map
const empty = Map(LEAF);

// construct a single item in map, the structure we build now:
// ET (Empty Tree)
//  tree (hold the k, v)
//  / \
// ET  ET
//
// singleton :: Ord k => k -> v -> Map k v
function singleton(k, v) {
  return tree2(empty, k, v, empty);
}

// emptyValue: Nothing - represent the key is not member of the given Map
// foundFn: this function will be called when the key is found.
// lookup :: Ord k => (forall a. m a) -> (forall a. a -> m a) -> k -> Map k v -> m v
function lookup(emptyValue, foundFn, k, tree0) {
  var tree = tree0, cmp, cmp2;
  while (true) {
    if (tree.tag === LEAF) {

      return emptyValue;
    } else if (tree.tag === TWO) {
      cpm = _compareFL(k, tree.k1);
      if (cmp === 0) {
        return foundFn(tree.v1);
      } else if (cmp === -1) {
        tree = tree.left; // LT, search left tree
      } else {
        tree = tree.right; // GT, search right tree
      }
      continue;
    } else if (tree.tag === THREE) {
      cmp = _compareFL(k, tree.k1);
      if (cmp === 0) {

        return foundFn(tree.v1);
      }
      cmp2 = _compareFL(k, tree.k2);
      if (cmp2 === 0) {

        return foundFn(tree.v2);
      }
      if (cmp === -1) {
        tree = tree.left; // LT, search left tree
        continue;
      }
      if (cmp2 === 1) {
        tree = tree.right; // GT, search right tree
        continue;
      }
      tree = tree.middle;
      continue;
    }
    // should never reached here
    throw new Error('OrdMap Invariant violation detected');
  }
}

// insert key and value to Map, if the key already exists replace it with new value.
// insert :: Ord k => k -> v -> Map k v -> Map k v
function insert(k, v, tree) {
  return insertDown(k, v, List(NIL), tree);
}


// -----------------------------------------------------------------------------
// ------------------------ Helper insert --------------------------------------
// -----------------------------------------------------------------------------
function fromZipper(xs0, tree0) {
  var xs = xs0, tree = tree0, head;
  while (true) {
    if (xs.tag === NIL) {
      return tree;
    }
    head = xs.head;
    if (head.tag === TWOLEFT) {
      tree = tree2(tree, head.k1, head.v1, head.tree1);
      xs = xs.tail;
      continue;
    } else if (head.tag === TWORIGHT) {
      tree = tree2(head.tree1, head.k1, head.v1, tree);
      xs = xs.tail;
      continue;
    } else if (head.tag === THREELEFT) {
      tree = tree3(tree3, head.k1, head.v1, head.tree1, head.k2, head.v2, head.tree2);
      xs = xs.tail;
      continue;
    } else if (head.tag === THREEMIDDLE) {
      tree = tree3(head.tree1, head.k1, head.v1, tree, head.k2, head.v2, head.tree2);
      xs = xs.tail;
      continue;
    } else if (head.tag === THREERIGHT) {
      tree = tree3(head.tree1, head.k1, head.v1, head.tree2, head.k2, head.v2, tree);
      xs = xs.tail;
      continue;
    }
    // this should never happen
    throw new Error('Internal OrdMap Error, Invalid list of TreeContext passed to fromZipper, ' +
                    'please send PR to Sanctuary Map Repo with detailed stack trace');
  }
}

function insertUp(xs0, kickup) {
  var xs = xs0, ku = kickup, h;
  while (true) {
    if (xs.tag === NIL) {
      return tree2(ku.tree1, ku.k, ku.v, ku.tree2);
    }
    h = xs.head;
    if (h.tag === TWOLEFT) {

      return fromZipper(xs.tail, tree3(ku.tree1, ku.k, ku.v, ku.tree2, h.k1, h.v1, h.tree1));
    } else if (h.tag === TWORIGHT) {

      return fromZipper(xs.tail, tree3(h.tree1, h.k1, h.v1, ku.tree1, ku.k, ku.v, ku.tree2));
    } else if (h.tag === THREELEFT) {
      ku = KickUp(tree2(ku.tree1, ku.k, ku.v, ku.tree2), h.k1, h.v1, tree2(h.tree1, h.k2, h.v2, h.tree2));
      xs = xs.tail;
      continue;
    } else if (h.tag === THREEMIDDLE) {
      ku = KickUp(tree2(h.tree1, h.k1, h.v1, ku.tree1), ku.k, ku.v, tree2(ku.tree2, h.k2, h.v2, h.tree2));
      xs = xs.tail;
      continue;
    } else if (h.tag === THREERIGHT) {
      ku = KickUp(tree2(h.tree1, h.k1, h.v1, h.tree2), h.k2, h.v2, tree2(ku.tree1, ku.k, ku.v, ku.tree2));
      xs = xs.tail;
      continue;
    }

    throw new Error('Internal OrdMap Error, Invalid arguments passed to insertUp, ' +
                    'please send PR to Sanctuary Map Repo with detailed stack trace');
  }
}

function insertDown(k, v, xs0, tree0) {
  var xs = xs0, t = tree0, cmp, cmp2;
  while (true) {
    if (t.tag === LEAF) {
      return insertUp(xs, KickUp(empty, k, v, empty));
    } else if (t.tag === TWO) {
      cmp = _compareFL(k, t.k1);
      if (cmp === 0) {
        // replace
        return fromZipper(xs, tree2(t.left, k, v, t.right))
      } else if (cmp === -1) {
        xs = List(CONS, TreeContext(TWOLEFT, t.k1, t.v1, t.right), xs);
        t  = t.left;
        continue;
      } else {
        xs = List(CONS, TreeContext(TWORIGHT, t.k1, t.v1, t.left), xs);
        t = t.right;
        continue;
      }
    } else if (t.tag === THREE) {
      cmp = _compareFL(k, t.k1);
      if (cmp === 0) {

        return fromZipper(xs, tree3(t.left, k, v, t.middle, t.k2, t.v2, t.right))
      }
      cmp2 = _compareFL(k, t.k2);
      if (cmp2 === 0) {

        return fromZipper(xs, tree3(t.left, t.k1, t.v1, t.middle, k, v, t.right));
      }
      if (cmp === -1) {
        xs = List(CONS, TreeContext(THREELEFT, t.k1, t.v1, t.middle, t.k2, t.v2, t.right), xs)
        t = t.left;
        continue;
      }
      if (cmp === 1 && cmp2 === -1) {
        xs = List(CONS, TreeContext(THREEMIDDLE, t.k1, t.v1, t.left, t.k2, t.v2, t.right), xs);
        t = t.middle;
        continue;
      }
      xs = List(CONS, TreeContext(THREERIGHT, t.k1, t.v1, t.left, t.k2, t.v2, t.middle), xs);
      t  = t.right;

      continue;
    }

    throw new Error('Internal OrdMap Error, Invalid arguments passed to insertUp, please send PR to Sanctuary Map Repo with detailed stack trace');
  }
}

// -----------------------------------------------------------------------------
// ------------------------------ Pop helper -----------------------------------
// -----------------------------------------------------------------------------
function maxTreePop(tree) {
  var t = tree;
  while (true) {
    if (t.tag === TWO && t.right.tag === LEAF) {
      return { key: t.k1, value: t.v1 };
    } else if (t.tag === TWO) {
      t = t.right;
      continue;
    } else if (t.tag === THREE && t.right.tag === LEAF) {
       return { key: t.k2, value: t.v2 };
    } else if (t.tag === THREE) {
      t = t.right;
      continue;
    }

    throw new Error('Internal OrdMap Error, Invalid arguments passed to maxTreePop, please send PR to Sanctuary Map Repo with detailed stack trace');
  }
}

// return 0 if a is equals to b
//        1 if a is greater than b
//        -1 otherwise
// This is internal function
function _compareFL(a, b) {
  if (a['fantasy-land/lte'] && b['fantasy-land/lte']) {
    return a['fantasy-land/lte'](b) ? (b['fantasy-land/lte'](a) ? 0 : -1) : 1;
  }
  // otherwise compare unsafe
  return a < b ? -1 : a === b ? 0 : 1;
}

function tree2(left, k, v, right) {
  return new Map(TWO, left, k, v, undefined, undefined, undefined, right)
}

function tree3(left, k1, v1, middle, k2, v2, right) {
  return new Map(THREE, left, k1, v1, middle, k2, v2, right)
}

function KickUp(tree1, k, v, tree2) {
  return { tree1: tree1, k: k, v: v, tree2: tree2 };
}

function TreeContext(tag, k1, v1, tree1, k2, v2, tree2) {
  return { tag: tag, k1 : k1, v1: v1, tree1: tree1, k2: k2, v2: v2, tree2: tree2 };
}

function List(tag, head, tail) {
  return  { tag: tag, head: head, tail: tail }
}