
function isObject(obj: any): boolean {
  return (typeof obj === 'object' && obj != null);
}

export function deepEqual(obj1: any, obj2: any): boolean {
  if (obj1 === obj2) return true;
  if (!isObject(obj1) || !isObject(obj2)) return false;
  return Object.keys(obj1).concat(Object.keys(obj2))
    .every(p => deepEqual(obj1[p], obj2[p]));
}

export function deepPatch(obj1: any, obj2: any): object | undefined {
  if (deepEqual(obj1, obj2)) return undefined;
  if (!isObject(obj1) || !isObject(obj2)) return obj2;
  const diff = {};
  Object.keys(obj2).forEach((k) => {
    if (!deepEqual(obj1[k], obj2[k])) {
      Object.assign(diff, { [k]: deepPatch(obj1[k], obj2[k]) });
    }
  });
  return diff;
}
