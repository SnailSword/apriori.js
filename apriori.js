var Apriori = (function() {

var assert = (function(global) {
    return function (x) {
        if (!x) {
            print('assertion failure at ' + new Error().stack);
            quit(3);
            return false;
        }
        return true;
    }
})(this);

var log = (typeof print !== 'undefined') ? print : console.log.bind(console);

var SupportMap = (function() {

    function SupportMap() {
        // Itemset -> integers
        this.map = {};
        // [Itemset]
        this.entries = [];
    };

    SupportMap.prototype.setup = function(entries) {
        this.clear();
        this.entries = entries;
    }

    SupportMap.prototype.clear = function() {
        this.map = {};
    }

    SupportMap.prototype.support = function(itemset) {
        var m = this.map;
        if (!m[itemset]) {
            var support = 0;
            for (var it of this.entries) {
                if (it.containsAll(itemset)) {
                    support += 1;
                }
            }
            m[itemset] = support;
        }
        return m[itemset];
    }

    SupportMap.prototype.relativeSupport = function(itemset) {
        return 100 * this.support(itemset) / this.entries.length;
    }

    SupportMap.prototype.alreadyProcessed = function(itemset) {
        return typeof this.map[itemset] !== 'undefined';
    }

    return new SupportMap;
})();

var LabelMap = (function() {

    function LabelMap() {
        // Name -> id
        this.nameInt = {}
        // Id -> name
        this.intName = {};
        this.size = 0;
    }

    LabelMap.prototype.lookupById = function(i) {
        return this.intName[i];
    }

    LabelMap.prototype.addName = function(name) {
        if (this.nameInt[name])
            return this.nameInt[name];

        var res = this.size++;
        this.nameInt[name] = res;
        this.intName[res]  = name;
        return res;
    }

    LabelMap.prototype.getAllProducts = function() {
        var list = [];
        for (var i in this.nameInt)
            list.push(this.nameInt[i]);
        return list;
    }

    LabelMap.prototype.clear = function() {
        this.nameInt.clear();
        this.intName.clear();
        this.size = 0;
    }

    return new LabelMap;
})();


var Itemset = function(copy) {
    this.set = {};
    if (typeof copy === 'undefined')
        return;
    for (var i in copy.set) {
        this.add(i);
    }
};
Itemset.prototype.add = function(x) {
    this.set[x] = true;
}
Itemset.prototype.has = function(x) {
    return typeof this.set[x] !== 'undefined';
}
Itemset.prototype.support = function() {
    return SupportMap.support(this);
}
Itemset.prototype.relativeSupport = function() {
    return SupportMap.relativeSupport(this);
}
Itemset.prototype.forEach = function(f) {
    for (var i in this.set) {
        f(i);
    }
}
Itemset.prototype.containsAll = function(other) {
    assert(other instanceof Array || other instanceof Itemset);
    var that = this;
    var retVal = true;
    other.forEach(function(i) {
        if (!that.has(i))
            retVal = false;
    });
    return retVal;
}
Itemset.prototype.toArray = function() {
    var a = [];
    this.forEach(function(v) {
        a.push(v)
    });
    return a
}
Itemset.prototype.subsetWithoutOneElement = function() {
    var list = []
    var itemseta = this.toArray();
    var size = this.size;
    var limit = Math.pow(2, size) - 1 | 0;
    for (var i = 0; i < limit; ++i) {
        var subset = new Itemset;
        for (var j = 0; j < size; ++j) {
            if (((i >> j) & 1) == 1)
                subset.add(itemseta[j]);
        }
        if (subset.size > 0 && subset.size == size - 1)
            list.push(subset);
    }
    return list;
};
Itemset.prototype.generateRules = function() {
    var rules = [];
    var list = this.toArray();
    var size = list.length;
    var limit = Math.pow(2, size) - 1 | 0;
    for (var i = 1; i < limit; ++i)
    {
        var premisse = new Itemset;
        var conclusion = new Itemset;
        for (var j = 0; j < size; ++j) {
            if (((i >> j) & 1) == 1)
                premisse.add(list[j]);
            else
                conclusion.add(list[j]);
        }
        rules.push(new Rule(premisse, conclusion));
    }
    return rules;
};
Itemset.prototype.toString = function() {
    var result = "";
    var count = 0;
    this.forEach(function (i) {
        if (count++ != 0) {
            result += ', ';
        }
        //result += i;
        result += LabelMap.lookupById(i);
    });
    return result;
}

Array.prototype.containsAll = function(other) {
    assert(other instanceof Array || other instanceof Itemset);
    var set = new Set(this);
    var retVal = true;
    other.forEach(function(el) {
        if (!set.has(el))
            retVal = false;
    });
    return retVal;
}

function Rule(premise, conclusion) {
    assert(premise instanceof Itemset);
    assert(conclusion instanceof Itemset);
    this.premise = premise;
    this.conclusion = conclusion;

    var union = new Itemset(premise);
    conclusion.forEach(function (c) {
        union.add(c);
    })

    this.support = union.support();
    this.relativeSupport = union.relativeSupport();
    this.confidence = 100 * (this.support) / premise.support();
}
Rule.prototype.toString = function() {
return this.premise.toString() + ' => ' + this.conclusion.toString() +
           '(support: ' + this.support + ' / confidence: ' +
           this.confidence + ')';
}

/**
 * The APriori Algorithm itself.
 *
 * Frequent itemsets of size N are said here to belong to the level N.
 *
 * The important steps of the algorithms are the following: 1) Computes
 * support and keep frequent itemsets of size 1. 2) Continue to generate new
 * itemsets while we have at least 2 different itemsets in the previous
 * level of itemsets. 3) Once we computed all the frequent itemsets,
 * generate all the rules.
 *
 * The generation of new itemsets of size N+1 from the frequent itemsets of
 * size N: - join step: let's take 2 different itemsets of size N with a
 * common prefix of size N-1 and mix them to form an itemset I_NEW of size
 * N+1. - prune step: check that all N-subsets of I_NEW are frequent
 * (APriori principle). - if I_NEW is possible, checks its support value
 * according to the support threshold.
 *
 * @param support
 * the threshold value of support (between 0 and 100%)
 * @param confidence
 * the threshold value of confidence (between 0 and 100%)
 * @return A list of valid rules satisfying both support and confidence
 * thresholds.
 */

function Apriori(source) {
    var transactions = [];
    for (var d of source) {
        var split = d.split(' ');
        var itemset = new Itemset;
        for (var word of split) {
            var id = LabelMap.addName(word);
            itemset.add(id);
        }
        transactions.push(itemset);
    }
    this.transactions = transactions;
}

Apriori.prototype.run = function(support, confidence) {
    log("Launching A Priori algorithm with following parameters:");
    log("Support (absolute) min: " + support);
    log("Confidence min: " + confidence);

    var begin = Date.now();
    SupportMap.setup(this.transactions);

    // Step 1 of the algorithm: generate frequent 1-itemsets
    log("Computing frequents of size 1...");
    var previousLevel = [];
    for (var i of LabelMap.getAllProducts()) {
        var temp = new Itemset;
        assert(temp instanceof Itemset);
        temp.add(i);

        var itemSupport = temp.relativeSupport();
        log("\t> Item: " + temp + " (support: " + itemSupport + ")");

        if (itemSupport >= support) {
            log("\t\t=> This item is a frequent itemset of size 1.");
            previousLevel.push(temp);
        } else {
            log("\t\t=> This item isn't a frequent itemset of size 1.");
        }
    }

    // Step 2: generate frequent itemsets of higher size
    log("Computing frequents of higher size...");
    var allFrequents = [];
    var nextLevel = null;
    var level = 1;

    // while loop
    while (previousLevel.length >= 2) {
        log("\t> Computing frequents of size " + ++level);
        // level == N+1 is the size of itemsets we want to generate.

        // reinits next level elements. Next level elements are here
        // elements of the size N+1.
        nextLevel = [];

        for (var i = 0, s = previousLevel.length; i < s; ++i) {
            var is1 = previousLevel[i];
            assert(is1 instanceof Itemset);
            // size N-1
            for (var j = i + 1; j < s; ++j) {
                var is2 = previousLevel[j];
                assert(is2 instanceof Itemset);

                // itemset of size N-1
                // We need to know whether is1 and is2 share the same
                // prefix; for this, we put
                // all elements of is2 in a list and remove the last
                // element. The list is the prefix
                var prefix = is2.toArray();
                var last = prefix.pop();

                // The generated itemset is is1 with the last element of is2
                var generated = new Itemset(is1);
                generated.add(last);

                if (!SupportMap.alreadyProcessed(generated)) {
                    // first condition: checks that is1 share contains the
                    // prefix, i.e. is1 and is2 have the same prefix
                    // second condition: checks that all subsets of size N-1
                    // of the generated element are frequent (APriori
                    // principle)
                    if (is1.containsAll(prefix) &&
                        previousLevel.containsAll(generated.subsetWithoutOneElement()))
                    {
                        var generatedSupport = generated.relativeSupport();
                        log("\t\t>> Generated itemset: " + generated
                                + " (support: " + generatedSupport + ")");

                        // checks the support
                        if (+generatedSupport >= +support) {
                            log("\t\t\t>> Frequent itemset.");
                            nextLevel.push(generated);
                        } else {
                            log("\t\t\t>> Not frequent.");
                        }
                    }
                }
            }
        }

        // All itemsets in nextLevel are frequent and of size N+1
        allFrequents = allFrequents.concat(nextLevel);
        log("\t> All the frequent itemsets of size " + level
                + " are the following: ");
        for (var itemset of nextLevel) {
            log("\t\t>> " + itemset);
        }

        // The elements of size N+1 are the previous elements of the
        // generation of elements of size N+2
        previousLevel = nextLevel;
    }

    // generate all possible rules
    log("There are " + allFrequents.length + " frequent itemsets");
    log("Generating rules...");
    var generatedRules = 0;
    var ruleList = [];
    for (var frequent of allFrequents) {
        assert(frequent instanceof Itemset);
        for (var r of frequent.generateRules()) {
            assert(r instanceof Rule);
            var ruleConfidence = r.confidence;
            log("\t> Considering the rule " + r + "...");
            if (ruleConfidence >= confidence) {
                log("\t\t=> Rule kept.");
                generatedRules += 1;
                ruleList.push(r);
            } else {
                log("\t\t=> Confidence too low.");
            }
        }
    }

    log(generatedRules + " rules have been generated.");
    log("Total duration: " + ((Date.now() - begin) / 1000.)+ "s");
    return ruleList;
}

return Apriori;

})();
