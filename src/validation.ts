import Ajv, { ValidateFunction } from "ajv";
import stringify from "fast-json-stable-stringify";
import { Mapping, ObjectMapping, NestedMapping } from "./es-types";

const ajv = new Ajv({ allErrors: true, coerceTypes: true });
const cache = new Map<string, ValidateFunction>();

const esTypeMap = new Map([
  ["boolean", ["boolean"]],
  ["byte", ["integer"]],
  ["date", ["string"]],
  ["double", ["number"]],
  ["float", ["number"]],
  ["geo_point", ["object"]],
  ["integer", ["integer"]],
  ["join", ["string", "object"]],
  ["keyword", ["string"]],
  ["long", ["integer"]],
  ["nested", ["array"]],
  ["object", ["object"]],
  ["short", ["integer"]],
  ["text", ["string"]],
]);

function translateField([field, mapping]: [string, Mapping]): Record<
  string,
  unknown
> {
  switch (mapping.type) {
    case undefined:
    case "object":
      return { [field]: translateObjectMapping(mapping) };
    case "nested":
      return { [field]: translateNestedMapping(mapping) };
    default:
      return {
        [field]: { type: [...(esTypeMap.get(mapping.type) || []), "null"] },
      };
  }
}

function translateNestedMapping(
  mapping: NestedMapping
): Record<string, unknown> {
  if (!mapping.properties) {
    return { type: ["array", "null"] };
  }
  return {
    type: ["array", "null"],
    items: {
      type: "object",
      properties: Object.assign(
        {},
        ...Object.entries(mapping.properties).map(translateField)
      ) as Record<string, unknown>,
    },
  };
}

export function translateObjectMapping(
  mapping: ObjectMapping
): Record<string, unknown> {
  return {
    type: ["object", "null"],
    additionalProperties: mapping.dynamic !== "strict",
    properties:
      mapping.properties &&
      (Object.assign(
        {},
        ...Object.entries(mapping.properties).map(translateField)
      ) as Record<string, unknown>),
  };
}

export function getValidatorForMapping(
  mappings: ObjectMapping
): ValidateFunction<unknown> {
  const key = stringify(mappings);
  if (!cache.has(key)) {
    cache.set(key, ajv.compile(translateObjectMapping(mappings)));
  }
  const value = cache.get(key);
  if (value) return value;
  throw new Error("Cache Error");
}
