declare type Value = unknown;
declare type TreeLike = {
    [key: string]: TreeLike | Value;
};
declare type ValueOrTree = Value | TreeLike;
export declare function deepEqual(obj1: unknown, obj2: unknown): boolean;
export declare function deepPatch(obj1: ValueOrTree, obj2: ValueOrTree): ValueOrTree;
export {};
