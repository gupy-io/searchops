import AJV from "ajv";
import { Mapping, ObjectMapping, NestedMapping } from "./es-types";

const ajv = new AJV({ allErrors: true, coerceTypes: true });

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

interface SyncValidationFunction extends AJV.ValidateFunction {
  (data: any): boolean;
  $async?: undefined;
}

export function getValidatorForMapping(
  mappings: ObjectMapping
): SyncValidationFunction {
  return ajv.compile(
    translateObjectMapping(mappings)
  ) as SyncValidationFunction;
}
