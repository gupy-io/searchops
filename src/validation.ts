import AJV from 'ajv';
import { Mapping, ObjectMapping, NestedMapping } from './es-types';

const ajv = new AJV({ allErrors: true, coerceTypes: true });

const esTypeMap = new Map([
  ['boolean', ['boolean']],
  ['byte', ['integer']],
  ['date', ['string']],
  ['double', ['number']],
  ['float', ['number']],
  ['geo_point', ['object']],
  ['integer', ['integer']],
  ['join', ['string', 'object']],
  ['keyword', ['string']],
  ['long', ['integer']],
  ['nested', ['array']],
  ['object', ['object']],
  ['short', ['integer']],
  ['text', ['string']],
]);

function translateField([field, mapping]: [string, Mapping]): object {
  switch (mapping.type) {
    case undefined:
    case 'object':
      // eslint-disable-next-line @typescript-eslint/no-use-before-define
      return { [field]: translateObjectMapping(mapping) };
    case 'nested':
      // eslint-disable-next-line @typescript-eslint/no-use-before-define
      return { [field]: translateNestedMapping(mapping) };
    default:
      return { [field]: { type: [...(esTypeMap.get(mapping.type) || []), 'null'] } };
  }
}

function translateNestedMapping(mapping: NestedMapping): object {
  if (!mapping.properties) {
    return { type: ['array', 'null'] };
  }
  return {
    type: ['array', 'null'],
    items: {
      type: 'object',
      properties: Object.assign(
        {},
        ...Object.entries(mapping.properties).map(translateField),
      ),
    },
  };
}

export function translateObjectMapping(mapping: ObjectMapping): object {
  return {
    type: ['object', 'null'],
    additionalProperties: mapping.dynamic !== 'strict',
    properties: mapping.properties && Object.assign(
      {},
      ...Object.entries(mapping.properties).map(translateField),
    ),
  };
}

export function getValidatorForMapping(mappings: ObjectMapping): AJV.ValidateFunction {
  return ajv.compile(translateObjectMapping(mappings));
}
