const removeUndefined = (obj) => {
  const copy = Object.assign({}, obj);
  Object.keys(copy).forEach((key) => {
    const value = obj[key];
    if (value) {
      if (value instanceof Date) {
        copy[key] = obj[key];
      } else if (typeof value === "object" && !Array.isArray(value)) {
        copy[key] = removeUndefined(value);
      } else if (typeof value === "string") {
        copy[key] = value.trim();
      } else if (
        Array.isArray(value) &&
        value.length > 0 &&
        typeof value[0] === "object"
      ) {
        copy[key] = value.map((v) => removeUndefined(v));
      }
    }
    if (copy[key] === undefined) {
      delete copy[key];
    }
  });
  return copy;
};

const removeUndefinedOfItems = (items) =>
  items.map((item) => removeUndefined(item));

module.exports = {
  removeUndefined,
  removeUndefinedOfItems,
};
