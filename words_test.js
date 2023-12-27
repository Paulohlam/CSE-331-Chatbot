"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
var assert = __importStar(require("assert"));
var words_1 = require("./words");
describe('words', function () {
    it('substitute', function () {
        // reps is empty.
        var words = ['test1', 'test1'];
        var reps1 = new Map();
        (0, words_1.substitute)(words, reps1);
        assert.deepStrictEqual(words, ['test', 'test1']);
        // single word replaced
        words = ['test', 'test1'];
        var reps2 = new Map([['test', 'test2']]);
        (0, words_1.substitute)(words, reps2);
        assert.deepStrictEqual(words, ['test2', 'test1']);
        // multiple words replaced
        words = ['test', 'test1', 'test3', 'test4'];
        var reps3 = new Map([
            ['test', 'test2'],
            ['test3', 'test5'],
        ]);
        (0, words_1.substitute)(words, reps3);
        assert.deepStrictEqual(words, ['test2', 'test1', 'test5', 'test4']);
        // words not in reps
        words = ['test', 'test1', 'test3', 'test4'];
        var reps4 = new Map([['test2', 'hey']]);
        (0, words_1.substitute)(words, reps4);
        assert.deepStrictEqual(words, ['test', 'test1', 'test3', 'test4']);
        // same replacement value replaced
        words = ['test', 'test1', 'test2'];
        var reps5 = new Map([
            ['test', 'test2'],
            ['test', 'test2'],
        ]);
        (0, words_1.substitute)(words, reps5);
        assert.deepStrictEqual(words, ['test2', 'test2', 'test2']);
    });
    it('replaceWords', function () {
        var repl = new Map([["a", ["a", "b", "c"]], ["d", ["e", "f"]]]);
        assert.deepStrictEqual((0, words_1.replaceWords)([], repl), []);
        assert.deepStrictEqual((0, words_1.replaceWords)(["the"], repl), ["the"]);
        assert.deepStrictEqual((0, words_1.replaceWords)(["a"], repl), ["a", "b", "c"]);
        assert.deepStrictEqual((0, words_1.replaceWords)(["the", "a", "dog"], repl), ["the", "a", "b", "c", "dog"]);
        assert.deepStrictEqual((0, words_1.replaceWords)(["the", "a", "dog", "d"], repl), ["the", "a", "b", "c", "dog", "e", "f"]);
    });
    it('splitWords', function () {
        assert.deepStrictEqual((0, words_1.splitWords)(""), []);
        assert.deepStrictEqual((0, words_1.splitWords)(" "), []);
        assert.deepStrictEqual((0, words_1.splitWords)("."), ["."]);
        assert.deepStrictEqual((0, words_1.splitWords)("a"), ["a"]);
        assert.deepStrictEqual((0, words_1.splitWords)("abc"), ["abc"]);
        assert.deepStrictEqual((0, words_1.splitWords)("ab,"), ["ab", ","]);
        assert.deepStrictEqual((0, words_1.splitWords)("ab,c"), ["ab", ",", "c"]);
        assert.deepStrictEqual((0, words_1.splitWords)("ab ,c"), ["ab", ",", "c"]);
        assert.deepStrictEqual((0, words_1.splitWords)("ab, c"), ["ab", ",", "c"]);
        assert.deepStrictEqual((0, words_1.splitWords)("ab , c"), ["ab", ",", "c"]);
        assert.deepStrictEqual((0, words_1.splitWords)("a b , c"), ["a", "b", ",", "c"]);
        assert.deepStrictEqual((0, words_1.splitWords)("abc, def! gh"), ["abc", ",", "def", "!", "gh"]);
        assert.deepStrictEqual((0, words_1.splitWords)("abc def  gh"), ["abc", "def", "gh"]);
    });
    it('wordsContain', function () {
        assert.strictEqual((0, words_1.wordsContain)([], ["a"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b"], ["a"]), 0);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "b"], ["a"]), 1);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "c", "d"], ["d"]), 3);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "d", "c", "e"], ["a"]), 1);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "d", "c", "e"], ["f"]), -1);
        assert.strictEqual((0, words_1.wordsContain)([], ["a", "b"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b"], ["a", "b"]), 0);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "b"], ["a", "b"]), 1);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "c", "d"], ["a", "c"]), 1);
        assert.strictEqual((0, words_1.wordsContain)(["c", "a", "d", "c", "e"], ["a", "c"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["a", "b", "c"]), 0);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["a", "b", "d"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["b", "c", "d"]), 1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["b", "c", "a"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["c", "d", "e"]), 2);
        assert.strictEqual((0, words_1.wordsContain)(["a", "b", "c", "d", "e"], ["c", "d", "c"]), -1);
        assert.strictEqual((0, words_1.wordsContain)(["A", "B", "C", "D", "E"], ["c", "d", "e"]), 2);
        assert.strictEqual((0, words_1.wordsContain)(["A", "B", "C", "D", "E"], ["c", "d", "c"]), -1);
    });
    it('joinWords', function () {
        assert.strictEqual((0, words_1.joinWords)([]), "");
        assert.strictEqual((0, words_1.joinWords)(["a"]), "a");
        assert.strictEqual((0, words_1.joinWords)([","]), ",");
        assert.strictEqual((0, words_1.joinWords)(["a", "!"]), "a!");
        assert.strictEqual((0, words_1.joinWords)(["a", "b"]), "a b");
        assert.strictEqual((0, words_1.joinWords)(["abc", "def"]), "abc def");
        assert.strictEqual((0, words_1.joinWords)(["a", ",", "b"]), "a, b");
        assert.strictEqual((0, words_1.joinWords)(["a", ",", "b", "c", "!"]), "a, b c!");
        assert.strictEqual((0, words_1.joinWords)(["a", ",", "b", "c", "!", "d"]), "a, b c! d");
        assert.strictEqual((0, words_1.joinWords)(["what", "?", "!", "?"]), "what?!?");
    });
});
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid29yZHNfdGVzdC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbIi4uL3NyYy93b3Jkc190ZXN0LnRzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFBQSw2Q0FBaUM7QUFDakMsaUNBQXdGO0FBR3hGLFFBQVEsQ0FBQyxPQUFPLEVBQUU7SUFFaEIsRUFBRSxDQUFDLFlBQVksRUFBRTtRQUNmLGlCQUFpQjtRQUNqQixJQUFJLEtBQUssR0FBRyxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQztRQUMvQixJQUFNLEtBQUssR0FBRyxJQUFJLEdBQUcsRUFBa0IsQ0FBQztRQUN4QyxJQUFBLGtCQUFVLEVBQUMsS0FBSyxFQUFFLEtBQUssQ0FBQyxDQUFDO1FBQ3pCLE1BQU0sQ0FBQyxlQUFlLENBQUMsS0FBSyxFQUFFLENBQUMsTUFBTSxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7UUFFakQsdUJBQXVCO1FBQ3ZCLEtBQUssR0FBRyxDQUFDLE1BQU0sRUFBRSxPQUFPLENBQUMsQ0FBQztRQUMxQixJQUFNLEtBQUssR0FBRyxJQUFJLEdBQUcsQ0FBaUIsQ0FBQyxDQUFDLE1BQU0sRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDM0QsSUFBQSxrQkFBVSxFQUFDLEtBQUssRUFBRSxLQUFLLENBQUMsQ0FBQztRQUN6QixNQUFNLENBQUMsZUFBZSxDQUFDLEtBQUssRUFBRSxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO1FBRWxELDBCQUEwQjtRQUMxQixLQUFLLEdBQUcsQ0FBQyxNQUFNLEVBQUUsT0FBTyxFQUFFLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQztRQUM1QyxJQUFNLEtBQUssR0FBRyxJQUFJLEdBQUcsQ0FBaUI7WUFDcEMsQ0FBQyxNQUFNLEVBQUUsT0FBTyxDQUFDO1lBQ2pCLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQztTQUNuQixDQUFDLENBQUM7UUFDSCxJQUFBLGtC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QUUsR0FBRyxFQUFFLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDO1FBRXZFLE1BQU0sQ0FBQyxXQUFXLENBQUMsSUFBQSxvQkFBWSxFQUFDLEVBQUUsRUFBRSxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDckQsTUFBTSxDQUFDLFdBQVcsQ0FBQyxJQUFBLG9CQUFZLEVBQUMsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztRQUM1RCxNQUFNLENBQUMsV0FBVyxDQUFDLElBQUEsb0JBQVksRUFBQyxDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztRQUNqRSxNQUFNLENBQUMsV0FBVyxDQUFDLElBQUEsb0JBQVksRUFBQyxDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxFQUFFLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7UUFDdEUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxJQUFBLG9CQUFZLEVBQUMsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDO1FBRTVFLE1BQU0sQ0FBQyxXQUFXLENBQUMsSUFBQSxvQkFBWSxFQUFDLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO1FBQ2hG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