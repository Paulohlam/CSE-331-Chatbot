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
var list_1 = require("./list");
describe('list', function () {
    it('len', function () {
        assert.deepEqual((0, list_1.len)(list_1.nil), 0);
        assert.deepEqual((0, list_1.len)((0, list_1.cons)(1, list_1.nil)), 1);
        assert.deepEqual((0, list_1.len)((0, list_1.cons)(2, list_1.nil)), 1);
        assert.deepEqual((0, list_1.len)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil))), 2);
        assert.deepEqual((0, list_1.len)((0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil)))), 3);
    });
    it('concat', function () {
        assert.deepEqual((0, list_1.concat)(list_1.nil, list_1.nil), list_1.nil);
        assert.deepEqual((0, list_1.concat)(list_1.nil, (0, list_1.cons)(1, list_1.nil)), (0, list_1.cons)(1, list_1.nil));
        assert.deepEqual((0, list_1.concat)(list_1.nil, (0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil))), (0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, list_1.nil), list_1.nil), (0, list_1.cons)(1, list_1.nil));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, list_1.nil), (0, list_1.cons)(2, list_1.nil)), (0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, list_1.nil), (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil))), (0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil))));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)), list_1.nil), (0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)), (0, list_1.cons)(3, list_1.nil)), (0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil))));
        assert.deepEqual((0, list_1.concat)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)), (0, list_1.cons)(3, (0, list_1.cons)(4, list_1.nil))), (0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, (0, list_1.cons)(4, list_1.nil)))));
    });
    it('rev', function () {
        assert.deepEqual((0, list_1.rev)(list_1.nil), list_1.nil);
        assert.deepEqual((0, list_1.rev)((0, list_1.cons)(1, list_1.nil)), (0, list_1.cons)(1, list_1.nil));
        assert.deepEqual((0, list_1.rev)((0, list_1.cons)(2, list_1.nil)), (0, list_1.cons)(2, list_1.nil));
        assert.deepEqual((0, list_1.rev)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil))), (0, list_1.cons)(2, (0, list_1.cons)(1, list_1.nil)));
        assert.deepEqual((0, list_1.rev)((0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil)))), (0, list_1.cons)(3, (0, list_1.cons)(2, (0, list_1.cons)(1, list_1.nil))));
    });
    it('compact_list', function () {
        assert.deepEqual((0, list_1.compact_list)(list_1.nil), []);
        assert.deepEqual((0, list_1.compact_list)((0, list_1.cons)(1, list_1.nil)), [1]);
        assert.deepEqual((0, list_1.compact_list)((0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil))), [1, 2]);
        assert.deepEqual((0, list_1.compact_list)((0, list_1.cons)(3, (0, list_1.cons)(2, (0, list_1.cons)(1, list_1.nil)))), [3, 2, 1]);
    });
    it('explode_array', function () {
        assert.deepEqual((0, list_1.explode_array)([]), list_1.nil);
        assert.deepEqual((0, list_1.explode_array)([1]), (0, list_1.cons)(1, list_1.nil));
        assert.deepEqual((0, list_1.explode_array)([1, 2]), (0, list_1.cons)(1, (0, list_1.cons)(2, list_1.nil)));
        assert.deepEqual((0, list_1.explode_array)([1, 2, 3]), (0, list_1.cons)(1, (0, list_1.cons)(2, (0, list_1.cons)(3, list_1.nil))));
    });
});
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoibGlzdF90ZXN0LmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2xpc3RfdGVzdC50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O0FBQUEsNkNBQWlDO0FBQ2pDLCtCQUFrRjtBQUdsRixRQUFRLENBQUMsTUFBTSxFQUFFO0lBRWYsRUFBRSxDQUFDLEtBQUssRUFBRTtRQUNSLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBQSxVQUFHLEVBQUMsVUFBRyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7UUFDOUIsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFBLFVBQUcsRUFBQyxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztRQUN2QyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsVUFBRyxFQUFDLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO1FBQ3ZDLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBQSxVQUFHLEVBQUMsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7UUFDaEQsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFBLFVBQUcsRUFBQyxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztJQUMzRCxDQUFDLENBQUMsQ0FBQztJQUVILEVBQUUsQ0FBQyxRQUFRLEVBQUU7UUFDWCxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLFVBQUcsRUFBRSxVQUFHLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQztRQUN4QyxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLFVBQUcsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsQ0FBQztRQUMxRCxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLFVBQUcsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQztRQUU1RSxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsRUFBRSxVQUFHLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsQ0FBQztRQUMxRCxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQztRQUM1RSxNQUFNLENBQUMsU0FBUyxDQUFDLElBQUEsYUFBTSxFQUFDLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLENBQUMsRUFDeEQsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFFcEMsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFBLGFBQU0sRUFBQyxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDNUUsTUFBTSxDQUFDLFNBQVMsQ0FBQyxJQUFBLGFBQU0sRUFBQyxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLEVBQ3hELElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLFVBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO1FBQ3BDLE1BQU0sQ0FBQyxTQUFTLENBQUMsSUFBQSxhQUFNLEVBQUMsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxVQUFHLENBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsQ0FBQyxFQUNqRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsSUFBQSxXQUFJLEVBQUMsQ0FBQyxFQUFFLElBQUEsV0FBSSxFQUFDLENBQUMsRUFBRSxJQUFBLFdBQUksRUFBQyxDQUFDLEVBQUUsVUFBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUMvQyxDQUFDLENBQUMsQ0FBQztJQUVILEVBQUUsQ0FBQyxLQUFLLEVBQUU7UUFDUixNQUFNLENBQUMsU0FBUyxDQUFD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