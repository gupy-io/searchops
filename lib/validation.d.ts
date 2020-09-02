import AJV from "ajv";
import { ObjectMapping } from "./es-types";
export declare function translateObjectMapping(mapping: ObjectMapping): object;
export declare function getValidatorForMapping(mappings: ObjectMapping): AJV.ValidateFunction;
