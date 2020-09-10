"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.getValidatorForMapping = exports.translateObjectMapping = void 0;
const ajv_1 = __importDefault(require("ajv"));
const ajv = new ajv_1.default({ allErrors: true, coerceTypes: true });
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
function translateField([field, mapping]) {
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
function translateNestedMapping(mapping) {
    if (!mapping.properties) {
        return { type: ["array", "null"] };
    }
    return {
        type: ["array", "null"],
        items: {
            type: "object",
            properties: Object.assign({}, ...Object.entries(mapping.properties).map(translateField)),
        },
    };
}
function translateObjectMapping(mapping) {
    return {
        type: ["object", "null"],
        additionalProperties: mapping.dynamic !== "strict",
        properties: mapping.properties &&
            Object.assign({}, ...Object.entries(mapping.properties).map(translateField)),
    };
}
exports.translateObjectMapping = translateObjectMapping;
function getValidatorForMapping(mappings) {
    return ajv.compile(translateObjectMapping(mappings));
}
exports.getValidatorForMapping = getValidatorForMapping;
