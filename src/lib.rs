use rand::{rngs::ThreadRng, RngCore};
use slotmap::{Key as _, SlotMap};
use std::cmp::Ordering;
use std::ops::Add;
slotmap::new_key_type! {
    pub struct TreapKey;
}

#[derive(Debug, Clone, Default)]
struct TreapNode<T> {
    value: T,
    priority: u64,
    left: TreapKey,
    right: TreapKey,
    parent: TreapKey,
    count: usize,
}

impl<T> TreapNode<T> {
    fn new(value: T, priority: u64) -> TreapNode<T> {
        TreapNode {
            value,
            priority,
            left: TreapKey::null(),
            right: TreapKey::null(),
            parent: TreapKey::null(),
            // how many nodes are beneath this one in the tree -- NOT its ordinal position
            count: 0,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TreapList<T, RNG: RngCore = ThreadRng> {
    nodes: SlotMap<TreapKey, TreapNode<T>>,
    rng: RNG,
    root: TreapKey,
}

impl<T, RNG: RngCore> TreapList<T, RNG> {
    pub fn new() -> Self
    where
        T: Default,
        RNG: Default,
    {
        Default::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.root = TreapKey::null();
    }

    fn nth(&self, mut n: usize) -> Option<TreapKey> {
        if n > self.len() {
            return None;
        }
        let mut cur = self.root;
        loop {
            let node = self.nodes.get(cur)?;
            let left_count = match self.nodes.get(node.left) {
                Some(lnode) => lnode.count + 1,
                None => 0,
            };
            match n.cmp(&left_count) {
                Ordering::Greater => {
                    n -= left_count;
                    n -= 1; //current node
                    cur = node.right;
                }
                Ordering::Equal => return Some(cur),
                Ordering::Less => {
                    cur = node.left;
                }
            }
        }
    }

    pub fn get(&self, n: usize) -> Option<&T> {
        self.nth(n).map(|key| &self.nodes[key].value)
    }

    pub fn get_mut(&mut self, n: usize) -> Option<&mut T> {
        self.nth(n).map(|key| &mut self.nodes[key].value)
    }

    fn insert_node(&mut self, node: TreapNode<T>, pos: usize) -> Option<TreapKey> {
        let key = self.nodes.insert(node);
        let (left, right) = self.split(self.root, pos);
        let left = self.merge(left, key);
        self.root = self.merge(left, right);
        self.nodes[self.root].parent = TreapKey::null();
        self.update(key);
        Some(key)
    }

    pub fn insert(&mut self, value: T, pos: usize) -> Option<TreapKey> {
        if self.len() < pos {
            return None;
        }
        let node = TreapNode::new(value, self.rng.next_u64());
        self.insert_node(node, pos)
    }

    pub fn push(&mut self, value: T) -> TreapKey {
        self.insert(value, self.len()).unwrap()
    }

    pub fn pop(&mut self) -> Option<T> {
        self.remove(self.len())
    }

    fn count(&self, key: TreapKey) -> usize {
        self.nodes.get(key).map(|node| node.count).unwrap_or(0)
    }

    // point the node's children to this one, and update the count of the current node
    fn update(&mut self, key: TreapKey) {
        let (left, right) = match self.nodes.get(key) {
            Some(n) => (n.left, n.right),
            None => return,
        };
        let mut count = 0;
        if let Some(node) = self.nodes.get_mut(left) {
            node.parent = key;
            count += node.count + 1;
        }
        if let Some(node) = self.nodes.get_mut(right) {
            node.parent = key;
            count += node.count + 1;
        }
        self.nodes[key].count = count;
    }

    fn merge(&mut self, left: TreapKey, right: TreapKey) -> TreapKey {
        if left.is_null() {
            return right;
        }
        if right.is_null() {
            return left;
        }
        if self.nodes[left].priority > self.nodes[right].priority {
            let lr = self.nodes[left].right;
            self.nodes[left].right = self.merge(lr, right);
            self.update(left);
            left
        } else {
            let rl = self.nodes[right].left;
            self.nodes[right].left = self.merge(left, rl);
            self.update(right);
            right
        }
    }

    fn split(&mut self, node: TreapKey, nth: usize) -> (TreapKey, TreapKey) {
        let (left, right) = match self.nodes.get(node) {
            Some(node) => (node.left, node.right),
            _ => return (TreapKey::null(), TreapKey::null()),
        };
        let left_count = self.count(left);
        if nth <= left_count {
            let (ll, lr) = self.split(left, nth);
            self.nodes[node].left = lr;
            self.update(node);
            (ll, node)
        } else {
            let (rl, rr) = self.split(right, nth - left_count);
            self.nodes[node].right = rl;
            self.update(node);
            (node, rr)
        }
    }

    pub fn remove(&mut self, n: usize) -> Option<T> {
        let key = self.nth(n)?;
        self.remove_node(key).map(|node| node.value)
    }

    fn remove_node(&mut self, key: TreapKey) -> Option<TreapNode<T>> {
        let node = self.nodes.remove(key)?;

        //update parent nodes' counts
        let mut cur = node.parent;
        while let Some(node) = self.nodes.get_mut(cur) {
            node.count -= 1;
            cur = node.parent;
        }

        let merged = self.merge(node.left, node.right);
        if let Some(parent_node) = self.nodes.get_mut(node.parent) {
            if parent_node.right == key {
                parent_node.right = merged;
            } else {
                parent_node.left = merged;
            }
            self.update(node.parent);
        }
        if key == self.root {
            self.root = merged;
        }

        Some(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
        let mut tpl = TreapList::<u32>::new();
        for n in 0..10 {
            tpl.push(n);
        }
        for n in 0..10 {
            assert_eq!(tpl.get(n).copied(), Some(n as u32));
        }
        let five = tpl.remove(5);
        assert_eq!(five, Some(5));
        for n in 0..9 {
            let expected = if n >= 5 { n + 1 } else { n };
            assert_eq!(tpl.get(n).copied(), Some(expected as u32), "{:#?}", tpl);
        }
    }

    #[test]
    fn remove_all() {
        let mut tpl = TreapList::<u32>::new();
        for n in 0..10 {
            tpl.push(n);
        }
        for _ in 0..100 {
            tpl.pop();
        }
    }
}
