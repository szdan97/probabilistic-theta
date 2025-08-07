package hu.bme.mit.theta.prob.analysis.asglazy

class TrieReachedSet<Data, Key>(
    val extractKeys: (Data) -> List<Key?>,
) {
    abstract inner class TrieNode {
        abstract fun get(key: List<Key?>): Set<Data>
        abstract fun delete(key: List<Key?>, d: Data): Boolean
        abstract fun add(key: List<Key?>, d: Data)
        abstract fun getAll(): Set<Data>
    }

    inner class DecisionNode(
        val knownNext: MutableMap<Key, TrieNode>, var unknownNext: TrieNode?
    ): TrieNode() {
        override fun get(key: List<Key?>): Set<Data> {
            val unknownRes = unknownNext?.get(key.drop(1)) ?: setOf()
            if(key.first() == null) {
                return unknownRes
            }
            return unknownRes union (knownNext[key.first()]?.get(key.drop(1)) ?: setOf())
        }

        override fun delete(key: List<Key?>, d: Data): Boolean {
            if(key.first() == null) return unknownNext?.delete(key.drop(1), d) ?: false
            else if (knownNext.contains(key.first())) {
                return knownNext[key.first()]!!.delete(key.drop(1), d)
            } else return false
        }

        override fun add(key: List<Key?>, d: Data) {
            fun newNode(): TrieNode {
                if(key.size == 1)
                    return LeafNode(hashSetOf())
                else
                    return DecisionNode(hashMapOf(), null)
            }

            if(key.first() == null) {
                if(unknownNext == null) {
                    unknownNext = newNode()
                }
                unknownNext!!.add(key.drop(1), d)
            } else {
                if(key.first() !in knownNext) {
                    knownNext[key.first()!!] = newNode()
                }
                knownNext[key.first()]!!.add(key.drop(1), d)
            }
        }

        override fun getAll(): Set<Data> {
            return knownNext.values.map { it.getAll() }.fold(setOf(), Set<Data>::union) union
                    (unknownNext?.getAll() ?: setOf())
        }
    }

    inner class LeafNode(
        val content: MutableSet<Data>
    ): TrieNode() {
        override fun get(key: List<Key?>): Set<Data> {
            return content
        }

        override fun delete(key: List<Key?>, d: Data): Boolean {
            return content.remove(d)
        }

        override fun add(key: List<Key?>, d: Data) {
            require(key.isEmpty())
            content.add(d)
        }

        override fun getAll(): Set<Data> {
            return content
        }
    }



    val root = DecisionNode(hashMapOf(), null)

    fun get(keys: List<Key?>): Set<Data> {
        return root.get(keys)
    }

    fun add(d: Data) {
        root.add(extractKeys(d), d)
    }

    fun delete(d: Data): Boolean {
        return root.delete(extractKeys(d), d)
    }

    fun get(like: Data): Set<Data> {
        return this.get(extractKeys(like))
    }

    fun getAll(): Set<Data> {
        return root.getAll()
    }
}